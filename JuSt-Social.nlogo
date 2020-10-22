; The name of this model is JuSt-Social (note: v1 was named "Social Interventions COVID-19 ABM")
; Copyright (c) 2020 Jennifer Badham
; It is released under the open source GNU General Public License version 3
; See the Info tab for an overview of the model and more detail about how it can be used.
; A detailed user manual with technical reference is also available.

; scenarios and adhoc analysis exports are in separate files
__includes
[ ; procedures for adhoc analysis
  "detailedExports.nls"    ; export patch or agent attributes (icnompatible with NetLogo Web)
  ; manages scenario routine. note that ALL scenarios must be named in interface chooser
  "scenariosMain.nls"      ; intervention triggers and demo scenarios
  ; specific scenarios
;  "scenariosLRF.nls"       ; scenarios developed for LRF reports
  "scenariosAdhoc.nls"     ; single scenario for testing, move to another script (and update chooser, scenariosMain) when satisfactory
  "scenariosPaper1.nls"    ; scenarios for the first article (presenting the model as tool)
]

globals
[ effective-R          ; cases per infected person
  week-E               ; tracks recent exposed count
  incidence            ; new cases as proportion
  prevalence-I         ; proportion contagious
  prevalence-all       ; proportion exposed but not yet recovered/dead
  pp-patch             ; agents created on each patch
  triggered?           ; whether interventions are operating

  ; reporters
  impact               ; proportion ever infected
  max-incidence        ; maximum incidence over the simulation
  max-prevalence       ; max prevalence (exposed + infectious) over simulation
  when-triggered       ; tick at which intervention trigger takes effect
  ; trackers for count, cumulative days in epidemic state
  tot-n-exposed
  tot-days-exposed
  tot-n-infectious
  tot-days-infectious
  tot-n-hospcrit
  tot-days-hospcrit
  admissions-hospital
  admissions-critical
  new-I
  new-R
  new-D
  blocked-bed
]

breed [people person]
people-own
[ ; disease state tracking
  epi-status      ; current epidemic state
  next-status     ; state to transition to
  next-when       ; when to transition epidemic state
  episodes        ; number of times get the disease (if immunity fails)
  when-symptoms   ; tick at which symptoms start
  ; personal factors concerning contact pattern and severity response
  prop-contact    ; adjustment for social distancing - 0 for isolation, 1 for no adjustment
  age-group       ; 0 is child, 1 is adult, 2 is older adult
  high-risk?      ; whether at higher risk of severity
  in-isolation?   ; whether currently in isolation
  isolation-end   ; tick at which isolation is to end
  informer?       ; whether informing contacts
  ; for reporting
  when-exposed    ; tick at which became exposed
  epi-duration    ; n ticks from exposure to immunity
  my-infected     ; agentset infected by self
]

; -------------------------------------------
; MAIN LOOPS
; -------------------------------------------

to setup
  clear-all
  ; controls whether using random seed
  ifelse randomise?
  [ set ScenarioNum new-seed ]
  [ random-seed ScenarioNum ]
  ; initialise the model
  initialise-globals
  setup-patches
  setup-people
  if region-selector != "off" [ scenario-trigger ]
  reset-ticks
  start-epidemic 1
  calculate-globals
end

to go
  ; check if still any infectious
  if all? people [epi-status = "susceptible" or epi-status = "immune" or epi-status = "dead"] [stop]
  ; housekeeping for start of day
  if prob-InfDeath + prob-InfHosp > 1 [ print "ERROR: total probabilities > 1" stop ]
  if prob-HospDeath + prob-HospCrit > 1 [ print "ERROR: total probabilities > 1" stop ]
  reset-counters
  trigger-update
  ; check scenario for change in settings
  if scenario-selector != "off" [revise-scenario]
  ; main functions
  move
  transition-status
  free-isolated
  symptomatic-actions
  transmit-infection
  ; housekeeping for end of day
  calculate-globals
  tick
end

to initialise-globals
  set effective-R 0
  set week-E []
  set incidence 0
  set prevalence-I 0
  set prevalence-all 0
  set pp-patch 12
  set triggered? false
  set when-triggered "no"
  set max-incidence 0
  set max-prevalence 0
  set tot-n-exposed 0
  set tot-days-exposed 0
  set tot-n-infectious 0
  set tot-days-infectious 0
  set tot-n-hospcrit 0
  set tot-days-hospcrit 0
  set admissions-hospital 0
  set admissions-critical 0
  set new-I 0
  set new-R 0
  set new-D 0
  set blocked-bed 0
end

; -------------------------------------------
; IMPLEMENTATION FUNCTIONS - SIMULATION
; -------------------------------------------

; infectious people have probability of exposing susceptible people on same patch
to transmit-infection
  ; people transmitting are infectious in community, in hospital treated as if isolated
  let transmitters people with [epi-status = "infectious" and not in-isolation?]
  ask people with [(epi-status = "infectious" and in-isolation?) or epi-status = "hospital" or epi-status = "critical"]
  [ if random-float 1 < (1 - isolation-efficacy)
    [ set transmitters (turtle-set transmitters self)
    ]
  ]

  ; people being transmitted to are susceptible, with some probability if isolated
  ask transmitters
  [ ask people-here with [epi-status = "susceptible"]
    [ ; remove effectively isolated
      if in-isolation? and (random-float 1 < isolation-efficacy) [ stop ]

      ; calculate transmission probability
      ; start with unadjusted transmission probability
      let prob-infect transmission-parameter
      ; adjust for age homophily
      if use-age-mixing? [ set prob-infect prob-infect * contact-age-homophily myself self ]
      ; reduce transmission probability for social distancing
      if triggered?
      [ set prob-infect prob-infect * prop-contact * [prop-contact] of myself
        if distancing-option = "ByContact" [ set prob-infect prob-infect * (1 - distancing-reduction) ]
      ]

      ; check if transmission occurs and, if so, call the exposure procedure
      ; self (and me) is the susceptible, and myself is the infector
      if random-float 1 < prob-infect
      [ let me self
        ask myself [set my-infected (turtle-set my-infected me)]
        SusExp myself       ; passes infector so can be informed if becomes symptomatic
      ]
    ]
  ]
end

; update status: exposed to infectious to recovered
; re-filter on next-when so don't progress multiple states
to transition-status
  ; select those changing status this tick
  let candidates people with [next-when = ticks]
  ; loss of immunity, become susceptible
  ask candidates with [next-status = "susceptible"][ImmSusc]
  ; exposed to infectious
  let candidates-E candidates with [epi-status = "exposed"]
  if any? candidates-E [ ask candidates-E [ ExpInf ] ]
  ; infectious to immune, hospital or dead by probability
  let candidates-I candidates with [epi-status = "infectious" and next-when = ticks]
  if any? candidates-I
  [ ask candidates-I
    [ (ifelse
      next-status = "immune" [makeImmune]
      next-status = "dead" [makeDead]
      next-status = "hospital" [admitHosp]
      [ type "ERROR: uncontrolled next status for infectious:" print next-status ])
    ]
  ]
  ; hospital to critical, dead or immune
  ; some in hospital for 0 days (eg immediately critical) so must occur before updating criticals
  let candidates-H candidates with [epi-status = "hospital" and next-when = ticks]
  if any? candidates-H
  [ ask candidates-H
    [ (ifelse
      next-status = "immune" [makeImmune]
      next-status = "critical" [hospCritical]
      next-status = "dead" [makeDead]
      [ type "ERROR: uncontrolled next status for hospital:" print next-status ])
    ]
  ]
  let candidates-C candidates with [epi-status = "critical" and next-when = ticks]
  if any? candidates-C
  [ ask candidates-C
    [ (ifelse
      next-status = "immune" [makeImmune]
      next-status = "dead" [makeDead]
      [ type "ERROR: uncontrolled next status for critical:" print next-status ])
    ]
  ]
end

; actions taken when a person becomes symptomatic
; voluntarily self-isolate and/or inform contacts
to symptomatic-actions
  ask people with [when-symptoms = ticks]
  [ ; set whether an informer when symptomatic regardless of whether informing is currently on
    set informer? random-float 1 < informers
    ; check whether policies operating
    if isolate-inform?
    [ ; self isolate with some probability, may already be isolating due to high risk status
      if random-float 1 < self-isolators
      [ set in-isolation? true
        set isolation-end max (list (ticks + SI-isolation-duration) isolation-end)
      ]
      ; inform contacts about potential exposure, future exposures check on exposure
      if isolate-inform? and informer?
      [ ask my-infected
        [ if random-float 1 < found-and-isolate
          [ set in-isolation? true
            set isolation-end max (list (ticks + SI-isolation-duration) isolation-end)
          ]
        ]
      ]
    ]
  ]
end

;----- EPIDEMIC STATUS CHANGES

; turtle procedure - status from susceptible to exposed
to SusExp [#infector]
  set epi-status "exposed"
  set color orange + 1
  set size 0.7
  set shape "dot"
  set when-exposed ticks
  set episodes episodes + 1
  ; assign next status and tick
  set next-status "infectious"
  let days get-days-tobe-exposed
  set next-when ticks + days
  ; isolate if infector already symptomatic
  if isolate-inform? and [informer?] of #infector and random-float 1 < found-and-isolate
  [ set in-isolation? true
    set isolation-end max (list (ticks + SI-isolation-duration) isolation-end)
  ]
  ; update global counters
  set tot-n-exposed tot-n-exposed + 1
  set tot-days-exposed tot-days-exposed + days
end

; turtle procedure - status from exposed to infectious, identifies next status too
to ExpInf
  set epi-status "infectious"
  set color orange
  set size 1
  set shape "dot"
  set new-I new-I + 1
  set my-infected (turtle-set nobody)
  ; assign next status and tick
  let days 0
  ; modify probabilities of severe (dead or hospital) for high/low risk
  let prob-DH prob-InfDeath + prob-InfHosp
  let prob-DH-low prob-DH / (prop-high-risk * relative-risk + 1 - prop-high-risk)
  let prob-DH-high relative-risk * prob-DH-low
  ; if severe, proportion to death (same for high/low risk)
  let DfromDH prob-InfDeath / prob-DH
  ; assign progression
  let draw random-float 1
  ifelse (high-risk? and draw < prob-DH-high) or (not high-risk? and draw < prob-DH-low)
  [ ; death or hospital as next state, new random draw to select which
    ifelse random-float 1 < DfromDH
    [ set next-status "dead"
      set days get-days-tobe-infectious-toDead
    ]
    [ set next-status "hospital"
      set days get-days-tobe-infectious-toHospital
    ]
  ]
  [ ; immune as next state
      set next-status "immune"
      set days get-days-tobe-infectious-toImmune
  ]
  ; symptomatic is some mild infections and all severe (hospital or dead), so exclude mild asymptomatic
  if not (next-status = "immune" and random-float 1 < mild-asymptomatic)
  [ let days-to-symptomatic min (list draw-poisson when-symptoms-if-I days) ; pre-symptomatic no longer than mild I state
    set when-symptoms ticks + days-to-symptomatic
  ]
  set next-when ticks + days
  ; update global counters
  set tot-n-infectious tot-n-infectious + 1
  set tot-days-infectious tot-days-infectious + days
end

; turtle procedure - status from infectious to hospital, identifies next status too
to admitHosp
  ; if hospital full, do not admit
  ifelse blocked-bed-effect? and count people with [epi-status = "hospital" or epi-status = "critical"] >= beds-H + beds-C
  [ set blocked-bed blocked-bed + 1
    let days 0
    ifelse random-float 1 < death-no-bed
    ; at home for days would normally be in hospital on the way to critical care
    [ set next-status "dead"
      set days get-days-tobe-hospital-toCritical
    ]
    ; at home for days would normally be in hospital
    [ set next-status "immune"
      set days get-days-tobe-hospital-toImmune
    ]
    set tot-days-infectious tot-days-infectious + days ; add days to community infectious total
    set next-when ticks + days
  ]
  ; if a bed available, admit and find duration and next status
  [ set epi-status "hospital"
    set color red
    set size 1
    set shape "house"
    ; admissions counter
    set admissions-hospital admissions-hospital + 1
    ; assign next status (immune or critical) and tick
    let days 0
    let draw random-float 1
    (ifelse
      draw < prob-HospDeath
      [ set next-status "dead"
        set days get-days-tobe-hospital-toDead
      ]
      draw < prob-HospDeath + prob-HospCrit
      [ set next-status "critical"
        set days get-days-tobe-hospital-toCritical
      ]
      [ set next-status "immune"
        set days get-days-tobe-hospital-toImmune
      ]
    )
   set next-when ticks + days
   ; update global counters
   set tot-n-hospcrit tot-n-hospcrit + 1
   set tot-days-hospcrit tot-days-hospcrit + days
 ]
end

; turtle procedure - status from hospital to critical, identifies next status too
to hospCritical
  set epi-status "critical"
  set color red - 2
  set size 1
  set shape "house"
  ; admissions counter
  set admissions-critical admissions-critical + 1
  ; assign next status (immune or dead) and tick
  let days 0
  ifelse random-float 1 < prob-CritDeath
  [ set next-status "dead"
    set days get-days-tobe-critical-toDead
  ]
  [ set next-status "immune"
    set days get-days-tobe-critical-toImmune
  ]
  set next-when ticks + days
  ; update global counters, already hospital so just add days
  set tot-days-hospcrit tot-days-hospcrit + days
end

; turtle procedure - status to immune (or susceptible if immunity not conferred)
to makeImmune
  ; random draw for retaining immunity indefinitely
  let draw random-float 1
  ifelse (epi-status = "infectious" and draw < immune-mild) or
         ((epi-status = "hospital" or epi-status = "critical") and draw < immune-severe)
  [ ; permanent immunity
    set next-status "nil"
    set next-when ticks - 1 ; no specific time for next status
  ]
  [ ; make susceptible in future
    set next-status "susceptible"
    set next-when ticks + 7 * immune-loss-when
  ]
  ; make immune
  set epi-status "immune"
  set color green + 1
  set shape "dot"
  set size 0.5
  set new-R new-R + 1
  set epi-duration ticks - when-exposed
end

; turtle procedure - status to dead
to makeDead
  set epi-status "dead"
  set color gray
  set shape "x"
  set size 0.5
  set new-D new-D + 1
  set epi-duration ticks - when-exposed
  ; assign next status and tick
  set next-status "nil"
  set next-when ticks - 1 ; makes ineligible as run passed this point
end

; turtle procedure - immune to susceptible
to ImmSusc
  set epi-status "susceptible"
  ; visually different than never infected
  set color blue - 1
  set size 0.8
  set shape "dot"
  ; reset own variables
  set when-exposed "na"
  set epi-duration "na"
  set my-infected (turtle-set nobody)
  set next-status "n/a"
  set next-when -1
  set informer? false
end

;----- other FUNCTIONAL procedures

to apply-distancing-policy
  ; give user interactive control of policies if requested
  if trigger-type = "interactive" [ set triggered? true ]
  ; All agents reduce contact rate by specified
  if distancing-option = "None" or distancing-option = "ByContact"
  [ ask people [ set prop-contact 1 ]
  ]
  if distancing-option = "AllPeople"
  [ ask people
    [ set prop-contact (1 - distancing-reduction)
    ]
  ]
  ; Some agents reduce contact rate to 0
  if distancing-option = "AllOrNone"
  [ ifelse high-risk-shielding?
    [ let low-risk-needed (distancing-reduction - prop-high-risk) / (1 - prop-high-risk)
      ask people with [not high-risk?]
      [ set prop-contact ifelse-value random-float 1 < low-risk-needed [0] [1]
      ]
      ask people with [high-risk?] [ set prop-contact 0 ]
    ]
    [ ask people
      [ set prop-contact ifelse-value random-float 1 < distancing-reduction [0] [1]
      ]
    ]
  ]
  ; apply isolation for high risk if set, may already be isolating due to symptoms policy
  if high-risk-shielding?
  [ ask people with [high-risk?]
    [ set in-isolation? true
      set isolation-end max (list (when-triggered + 7 * HR-shield-duration) isolation-end)
    ]
  ]
end

; moves specified proportion of people in a random direction that avoids passing world edges
to move
  ; those in hospital don't move, immune and dead are irrelevant so excluded
  let movers people with [ epi-status = "susceptible" or epi-status = "exposed" or epi-status = "infectious" ]
  ; short distance
  let num-move-short round (prop-move-short * (ifelse-value triggered? [1 - move-reduction-short][1]) * count movers)
  ask n-of num-move-short movers
  [ face one-of neighbors
    right -20 + random 20
    forward 1
  ]
  ; long distance
  let num-move-long round (prop-move-long * (ifelse-value triggered? [1 - move-reduction-long][1]) * count movers)
  ask n-of num-move-long movers
  [ face one-of neighbors
    right -20 + random 20
    forward 3
  ]
end

; end period of isolation at scheduled tick
to free-isolated
  ask people with [isolation-end = ticks]
  [ set isolation-end 0
    set in-isolation? false
  ]
end

; -------------------------------------------
; IMPLEMENTATION FUNCTIONS - SCENARIOS see included source file scenariosMain
; -------------------------------------------

; -------------------------------------------
; IMPLEMENTATION FUNCTIONS - SETUP
; -------------------------------------------

to setup-patches
  ask patches
  [ set pcolor white
  ]
end

to setup-people
  ask patches
  [ sprout-people pp-patch
    [ set epi-status "susceptible"
      ; visualisation
      set color blue + 1
      set size 0.5
      set shape "default"
      ; epidemic progression
      set when-exposed "na"
      set epi-duration "na"
      set my-infected (turtle-set nobody)
      set episodes 0
      set next-status "n/a"
      set next-when -1
      ; personal attributes
      set prop-contact 1
      set age-group assign-age
      set high-risk? random-float 1 < prop-high-risk
      set in-isolation? false
      set isolation-end 0
      set informer? false
      forward random-float 0.6
    ]
  ]
end

to start-epidemic [#exposed]
  ask n-of #exposed people with [epi-status = "susceptible"]
  [ SusExp one-of people   ; pass random person as infector for isolation check
  ]
end

; -------------------------------------------
; UTILITY FUNCTIONS
; -------------------------------------------

to apply-defaults
  set transmission-parameter 0.03
  set prop-move-short 0.4
  set prop-move-long 0.15
  set prob-InfHosp 0.07 ; Average suggested by ONS infection surveys and lagged admissions
  set prob-InfDeath 0.015 ; derived from deaths in hospital is 65% of covid-attributed deaths, 7.0% admitted
  set prob-HospCrit 0.17 ; ISARIC study in UK
  set prob-HospDeath 0.30 ; ISARIC study in UK
  set prob-CritDeath 0.43 ; ICNARC report 29 May 2020 (Table 9)
  set immune-mild 1
  set immune-severe 1
  set immune-loss-when 12
  set beds-H 40
  set beds-C 3
  set prop-high-risk 0.04 ; size of shielded patient list
  set relative-risk 4 ; admission risk derived (based on admission risk for age 70+)
end

to reset-counters
  set admissions-hospital 0
  set admissions-critical 0
  set new-I 0
  set new-R 0
  set new-D 0
end

to calculate-globals
  ; estimates effective-R with prior week new exposed per infectious in the community and I duration (ignores hospitalised)
  set week-E fput (count people with [when-exposed = ticks]) week-E
  if length week-E > 7 [set week-E sublist week-E 0 7]
  let n-infected count people with [epi-status = "infectious"]
  set effective-R ifelse-value n-infected > 0 [sum week-E * (tot-days-infectious / tot-n-infectious) / (7 * n-infected)][0]
  ; incidence is new cases today as population proportion
  set incidence count people with [when-exposed = ticks] / count people
  ; prevalence is currently infectious
  set prevalence-I count people with [epi-status = "infectious" or epi-status = "hospital" or epi-status = "critical"] / count people
  set prevalence-all count people with [epi-status = "exposed" or epi-status = "infectious" or epi-status = "hospital" or epi-status = "critical"] / count people
  ; update maximums
  if incidence > max-incidence [ set max-incidence incidence ]
  if prevalence-all > max-prevalence [ set max-prevalence prevalence-all ]
  set impact 1 - count people with [epi-status = "susceptible" and episodes = 0] / count people
end

to-report draw-poisson [#mean] ; from Knuth 1997, as cited in wikipedia! (but did test, looks right)
  let L exp(- #mean)
  let k 0
  let p 1
  while [p > L]
  [ set k k + 1
    set p p * random-float 1
  ]
  report k - 1
end

to-report draw-wtd [#vals #wts]  ; weighted draw from list of values
  if length #vals != length #wts [ print "ERROR: weighted random draw" report -1 ]
  let draw random-float sum #wts
  let idx 0
  while [draw > 0]
  [ set draw draw - item idx #wts
    set idx idx + 1
  ]
  report item (idx - 1) #vals
end

to-report assign-age
  let age [ 0 1 2 ]
  let weights [ 0.211 0.657 0.132 ]
  report draw-wtd age weights
end

; uses modified POLYMOD data (symmetric, 11 contacts) for age relative risk of contact
to-report contact-age-homophily [#person1 #person2]
  let age-weights item [age-group] of #person1 [[3.447 0.881 0.247][0.881 1.136 0.460][0.247 0.460 1.040]]
  report item [age-group] of #person2 age-weights
end

; start or end distancing policies
to trigger-update
  if when-triggered = "no"; check to start social distancing interventions
  [ set triggered? check-triggered?
    if triggered?
    [ set when-triggered ticks
      apply-distancing-policy
    ]
  ]
  if triggered? and ticks > when-triggered + 7 * intervention-duration and trigger-type != "interactive" ; end interventions
  [ set triggered? false
  ]

end

; sets the flag to show interventions are operating, and when
to-report check-triggered?
  if trigger-type = "interactive" [ report true ]
  if trigger-type = "days" [ report ticks >= trigger-level - 1 ]
  let in-hospital count people with [epi-status = "hospital" or epi-status = "critical"]
  if trigger-type = "hospital" [ report in-hospital >= trigger-level ]
  if trigger-type = "cases" [ report tot-n-exposed >= trigger-level ]
end

; monitor for whether distancing currently applied
to-report policy-status
  report ifelse-value triggered? ["YES"] ["no"]
end

;----- DISTRIBUTION DRAWS for ticks to next status change

; draw days exposed until infectious
to-report get-days-tobe-exposed
  ; from Lauer, lognormal distribution with 1.621 and 0.418
  let draw random-normal 1.621 0.418
  report round(exp(draw))
end

to-report get-days-tobe-infectious-toImmune
  ; ECDC Q&A states infectious period 7-12 days for moderate cases (no source)
  let days [ 7 8 9 10 11 12 ]
  let weights [ 1 1 1 1 1 1 ]
  report draw-wtd days weights
end

; draw days infectious
to-report get-days-tobe-infectious-toHospital
  ; from digitised ECDC UK onset to hospitalisation + 1 day for pre-symptoms
  let days [ 1 2 3 4 5 6 7 8 9 10 11 12 13 ]
  let weights [ 0.063 0.083 0.104 0.125 0.114 0.103 0.092 0.081 0.069 0.058 0.047 0.036 0.025 ]
  report draw-wtd days weights
end

to-report get-days-tobe-infectious-toDead
  ; same distribution as infectious to hospital, adds 1 day for dying instead of going to hospital
  let days [ 2 3 4 5 6 7 8 9 10 11 12 13 14 ]
  let weights [ 0.063 0.083 0.104 0.125 0.114 0.103 0.092 0.081 0.069 0.058 0.047 0.036 0.025 ]
  report draw-wtd days weights
end

; draw from empirical distribution, days in hospital
to-report get-days-tobe-hospital-toCritical
  ; inspired by ICNARC Table 2, with quartiles at 0, 1, 3 and mean 2.4
  let days [ 0 1 2 3 4 5 6 7 ]
  let weights [ 0.30 0.25 0.15 0.10 0.05 0.05 0.05 0.05 ]
  report draw-wtd days weights
end

to-report get-days-tobe-hospital-toImmune
  ; from Imperial report 17 Fig 2A (ignores H vs C), discharged alive
  let days [ 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 "tail"]
  let weights [ 0.032 0.097 0.091 0.095 0.096 0.065 0.061 0.067 0.071 0.023 0.033 0.017 0.033 0.023
    0.031 0.015 0.025 0.008 0.012 0.006 0.000 0.018 0.028 0.053 ]
  let draw draw-wtd days weights
  ifelse draw = "tail"
  [ report 24 + random 7 ] ; uniform 24-30 days length of stay
  [ report draw ]
end

to-report get-days-tobe-hospital-toDead
  ; from Imperial report 17 Fig 2A (ignores H vs C), died in hospital
  let days [ 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 "tail"]
  let weights [ 0.029 0.089 0.039 0.139 0.114 0.066 0.070 0.099 0.070 0.041
    0.031 0.008 0.017 0.033 0.017 0.043 0.039 0.056 ]
  let draw draw-wtd days weights
  ifelse draw = "tail"
  [ report 18 + random 4 ] ; uniform 18-21 days length of stay
  [ report draw ]
end

; draw from empirical distribution, days in critical care
to-report get-days-tobe-critical-toImmune
  ; from ICNARC 29 May 2020, Figure 11
  let days [ 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 "tail" ]
  let weights [ 0.057 0.068 0.047 0.067 0.047 0.041 0.022 0.025 0.052 0.011 0.036 0.022 0.020
    0.027 0.031 0.016 0.011 0.025 0.016 0.016 0.020 0.011 0.022 0.009 0.022 0.011 0.014 0.011 0.223]
  let draw draw-wtd days weights
  ifelse draw = "tail"
  [ report 29 + random 28 ] ; uniform 29-56 days length of stay
  [ report draw ]
end

to-report get-days-tobe-critical-toDead
  ; from ICNARC 29 May 2020, Figure 11
  let days [ 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 "tail" ]
  let weights [ 0.060 0.026 0.055 0.069 0.057 0.069 0.041 0.055 0.048 0.043 0.026 0.048 0.036
    0.022 0.026 0.036 0.026 0.014 0.029 0.019 0.007 0.022 0.014 0.007 0.012 0.007 0.007 0.014 0.105]
  let draw draw-wtd days weights
  ifelse draw = "tail"
  [ report 29 + random 28 ] ; uniform 29-56 days length of stay
  [ report draw ]
end
@#$#@#$#@
GRAPHICS-WINDOW
437
124
855
543
-1
-1
10.0
1
10
1
1
1
0
0
0
1
-20
20
-20
20
1
1
1
days
30.0

BUTTON
507
37
607
112
NIL
setup
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

BUTTON
611
37
671
72
day
go
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

BUTTON
611
77
671
112
week
repeat 7 [go]
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

BUTTON
675
37
775
112
go
go
T
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

TEXTBOX
30
15
260
49
Epidemic Progression
24
15.0
1

SLIDER
30
66
210
99
transmission-parameter
transmission-parameter
0
0.15
0.03
0.005
1
NIL
HORIZONTAL

SLIDER
30
101
210
134
prop-move-short
prop-move-short
0
0.5
0.4
0.05
1
NIL
HORIZONTAL

SLIDER
30
134
210
167
prop-move-long
prop-move-long
0
0.2
0.15
0.01
1
NIL
HORIZONTAL

SWITCH
230
119
420
152
blocked-bed-effect?
blocked-bed-effect?
1
1
-1000

INPUTBOX
230
59
290
119
beds-H
40.0
1
0
Number

INPUTBOX
290
59
350
119
beds-C
3.0
1
0
Number

SLIDER
230
151
420
184
death-no-bed
death-no-bed
0
1
0.8
0.05
1
NIL
HORIZONTAL

MONITOR
353
69
420
114
Blocked
blocked-bed
0
1
11

PLOT
20
199
420
349
Epidemic
NIL
NIL
0.0
10.0
0.0
0.01
true
true
"" ""
PENS
"Prevalence (EI)" 1.0 0 -16777216 true "" "plot prevalence-all"
"Prop Infectious" 1.0 0 -7500403 true "" "plot prevalence-I"
"Incidence (E)" 1.0 0 -2674135 true "" "plot incidence"

MONITOR
340
294
405
339
Impact
impact
3
1
11

PLOT
20
365
210
515
Admissions
NIL
NIL
0.0
10.0
0.0
10.0
true
true
"" ""
PENS
"H" 1.0 0 -2674135 true "" "plot admissions-hospital"
"C" 1.0 0 -8053223 true "" "plot admissions-critical"

PLOT
20
515
210
665
Occupancy
NIL
NIL
0.0
10.0
0.0
10.0
true
true
"" ""
PENS
"H" 1.0 0 -2674135 true "" "plot count people with [epi-status = \"hospital\"]"
"H beds" 1.0 2 -2674135 false "" "plot beds-H"
"C" 1.0 0 -8053223 true "" "plot count people with [epi-status = \"critical\"]"
"C beds" 1.0 2 -8053223 false "" "plot beds-C"

PLOT
220
365
420
515
New Cases (Infectious)
NIL
NIL
0.0
10.0
0.0
10.0
true
false
"" ""
PENS
"default" 1.0 1 -7500403 true "" "plot new-I"

MONITOR
225
417
281
462
Inf (-H)
count people with [epi-status = \"infectious\"]
0
1
11

PLOT
220
515
420
665
Daily Deaths
NIL
NIL
0.0
10.0
0.0
10.0
true
false
"" ""
PENS
"default" 1.0 1 -16777216 false "" "plot new-D"

MONITOR
223
565
280
610
Dead
count people with [epi-status = \"dead\"]
0
1
11

MONITOR
460
562
520
607
People
count people
0
1
11

MONITOR
530
562
585
607
Mix R0
(1 - (1 - transmission-parameter) ^ ifelse-value tot-n-exposed > 0 [tot-days-infectious / tot-n-infectious] [0]) * (pp-patch - 1)
2
1
11

MONITOR
585
562
640
607
R
effective-R
2
1
11

MONITOR
530
610
585
655
E days
ifelse-value tot-n-exposed > 0 [tot-days-exposed / tot-n-exposed] [0]
1
1
11

MONITOR
585
610
640
655
I days
ifelse-value tot-n-infectious > 0 [tot-days-infectious / tot-n-infectious] [0]
2
1
11

MONITOR
640
610
695
655
HC LoS
ifelse-value tot-n-hospcrit > 0 [tot-days-hospcrit / tot-n-hospcrit] [0]
2
1
11

SLIDER
655
563
855
596
isolation-efficacy
isolation-efficacy
0.8
1
0.9
0.01
1
NIL
HORIZONTAL

TEXTBOX
875
15
1042
43
Interventions
24
15.0
1

BUTTON
1150
37
1440
87
All Interventions Off
interventions-off
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

TEXTBOX
875
80
1030
100
Social Distancing
14
15.0
1

TEXTBOX
885
111
1440
203
Select what is meant by social distancing and how strongly the distancing works.\n(1) ByContact: the probability of a tranmitting contact is reduced by the specified proportion.\n(2) AllPeople: everyone reduces their activity (attempted contacts) by the specified proportion.\n(3) AllOrNone: the given proportion of people isolate (includes high risk if isolation also selected), but others make no reduction.
11
0.0
1

CHOOSER
885
205
1060
250
distancing-option
distancing-option
"None" "ByContact" "AllPeople" "AllOrNone"
0

SLIDER
885
250
1060
283
distancing-reduction
distancing-reduction
0
1
0.25
0.05
1
NIL
HORIZONTAL

SWITCH
1065
205
1240
238
high-risk-shielding?
high-risk-shielding?
1
1
-1000

SLIDER
1065
238
1240
271
HR-shield-duration
HR-shield-duration
1
52
15.0
1
1
weeks
HORIZONTAL

BUTTON
1250
206
1440
239
Apply Distancing and Isolation
apply-distancing-policy
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

TEXTBOX
1250
245
1440
278
To change during the run, PRESS the button after setting changes
11
15.0
1

TEXTBOX
885
295
1224
356
Movement restrictions are a form of distancing as people come only in contact with the same other people repeatedly, reducing mixing between infectious and susceptible people. 
11
0.0
1

SLIDER
1265
287
1440
320
move-reduction-short
move-reduction-short
0
1
0.0
0.05
1
NIL
HORIZONTAL

SLIDER
1265
320
1440
353
move-reduction-long
move-reduction-long
0
1
0.0
0.05
1
NIL
HORIZONTAL

TEXTBOX
885
388
1194
407
When does the social distancing policy start (and stop)?
11
0.0
1

TEXTBOX
885
365
1050
385
Social Distancing Timing
12
15.0
1

CHOOSER
885
408
1000
453
trigger-type
trigger-type
"interactive" "days" "hospital" "cases"
3

INPUTBOX
1000
408
1115
468
trigger-level
200.0
1
0
Number

TEXTBOX
1135
413
1330
524
Time Based\n> interactive - operates throughout\n> days - after given number of days\nEpidemic Based\n> hospital - people in hospital\n> cases - people infectious
11
0.0
1

SLIDER
885
468
1115
501
intervention-duration
intervention-duration
1
52
12.0
1
1
weeks
HORIZONTAL

MONITOR
1320
403
1400
448
On?
policy-status
0
1
11

MONITOR
1320
448
1400
493
Triggered at
when-triggered
0
1
11

TEXTBOX
873
524
1034
544
Response to Symptoms
14
15.0
1

SWITCH
885
555
1065
588
isolate-inform?
isolate-inform?
1
1
-1000

SLIDER
885
588
1065
621
mild-asymptomatic
mild-asymptomatic
0
1
0.45
0.05
1
NIL
HORIZONTAL

TEXTBOX
1075
550
1440
620
Self-isolation and informing contacts (if switched on) apply regardless of whether distancing interventions have been triggered.\n\nOnly some of mildly infected may show symptoms (plus all in hospital).
11
0.0
1

TEXTBOX
885
645
1075
740
Self-isolating people reduce contacts as soon as they get any symptoms. Informers attempt to notify recent contacts of potential exposure, some of whom choose to isolate.
11
0.0
1

TEXTBOX
1090
625
1155
650
Self-Isolate
12
15.0
1

SLIDER
1090
645
1265
678
self-isolators
self-isolators
0
1
0.0
0.05
1
NIL
HORIZONTAL

SLIDER
1090
678
1265
711
SI-isolation-duration
SI-isolation-duration
7
21
14.0
1
1
days
HORIZONTAL

TEXTBOX
1265
625
1400
650
Inform Contacts
12
15.0
1

SLIDER
1265
645
1440
678
informers
informers
0
1
0.0
0.05
1
NIL
HORIZONTAL

SLIDER
1265
678
1440
711
found-and-isolate
found-and-isolate
0
1
0.4
0.05
1
NIL
HORIZONTAL

SLIDER
1265
711
1440
744
IC-isolation-duration
IC-isolation-duration
7
21
14.0
1
1
days
HORIZONTAL

TEXTBOX
23
789
1223
870
----- Scroll down for advanced settings and outputs -----
48
105.0
1

SWITCH
1113
866
1239
899
randomise?
randomise?
0
1
-1000

INPUTBOX
1239
866
1365
926
ScenarioNum
8.82891943E8
1
0
Number

TEXTBOX
30
866
250
896
Disease Progression
14
15.0
1

BUTTON
220
900
330
933
Use Defaults
apply-defaults
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

SLIDER
30
899
205
932
prob-InfDeath
prob-InfDeath
0
0.05
0.015
0.0025
1
NIL
HORIZONTAL

SLIDER
30
932
205
965
prob-InfHosp
prob-InfHosp
0
0.25
0.07
0.005
1
NIL
HORIZONTAL

SLIDER
30
965
205
998
prob-HospDeath
prob-HospDeath
0
1
0.3
0.01
1
NIL
HORIZONTAL

SLIDER
30
998
205
1031
prob-HospCrit
prob-HospCrit
0
1
0.17
0.01
1
NIL
HORIZONTAL

SLIDER
30
1031
205
1064
prob-CritDeath
prob-CritDeath
0
1
0.43
0.01
1
NIL
HORIZONTAL

MONITOR
220
943
330
988
Community IFR%
100 * prob-InfDeath
2
1
11

MONITOR
220
988
330
1033
Hospital IFR%
100 * (prob-HospDeath + prob-HospCrit * prob-CritDeath)
1
1
11

MONITOR
220
1033
330
1078
Overall IFR%
100 * (prob-InfDeath + prob-InfHosp * (prob-HospDeath + prob-HospCrit * prob-CritDeath))
1
1
11

MONITOR
220
1078
330
1123
CFR%
(100 * (prob-InfDeath + prob-InfHosp * (prob-HospDeath + prob-HospCrit * prob-CritDeath))) / (1 - mild-asymptomatic + prob-InfHosp * mild-asymptomatic)
1
1
11

SLIDER
30
1084
205
1117
immune-mild
immune-mild
0
1
1.0
0.01
1
NIL
HORIZONTAL

SLIDER
30
1117
205
1150
immune-severe
immune-severe
0
1
1.0
0.01
1
NIL
HORIZONTAL

SLIDER
30
1150
205
1183
immune-loss-when
immune-loss-when
4
26
12.0
1
1
weeks
HORIZONTAL

SLIDER
30
1214
205
1247
when-symptoms-if-I
when-symptoms-if-I
0
2.5
1.0
0.25
1
days
HORIZONTAL

SLIDER
30
1247
205
1280
max-presymptomatic
max-presymptomatic
1
6
3.0
1
1
days
HORIZONTAL

TEXTBOX
220
1214
330
1280
Truncated Poisson days from infectious to symptoms, by mean and max.
11
0.0
1

TEXTBOX
360
866
530
886
Epidemic Progress
14
15.0
1

PLOT
360
896
720
1096
Prevalence by age
NIL
NIL
0.0
10.0
0.0
0.1
true
true
"" ""
PENS
"older" 1.0 0 -2674135 true "" "plot count people with [age-group = 2 and (epi-status = \"infectious\" or epi-status = \"hospital\" or epi-status = \"critical\")] / count people with [age-group = 2]"
"adult" 1.0 0 -13345367 true "" "plot count people with [age-group = 1 and (epi-status = \"infectious\" or epi-status = \"hospital\" or epi-status = \"critical\")] / count people with [age-group = 1]"
"child" 1.0 0 -16777216 true "" "plot count people with [age-group = 0 and (epi-status = \"infectious\" or epi-status = \"hospital\" or epi-status = \"critical\")] / count people with [age-group = 0]"

PLOT
360
1116
540
1266
Reproduction (week)
NIL
NIL
0.0
10.0
0.0
5.0
true
false
"" ""
PENS
"default" 1.0 0 -16777216 true "" "plot effective-R"

PLOT
540
1116
720
1266
R distribution
NIL
NIL
0.0
15.0
0.0
10.0
true
false
"" ""
PENS
"default" 1.0 1 -16777216 false "" "histogram [count my-infected] of people with [epi-status = \"immune\" or epi-status = \"dead\"]"

TEXTBOX
765
866
985
886
Population and Interventions
14
15.0
1

SWITCH
765
910
945
943
use-age-mixing?
use-age-mixing?
1
1
-1000

SLIDER
765
963
945
996
prop-high-risk
prop-high-risk
0
0.2
0.04
0.01
1
NIL
HORIZONTAL

SLIDER
765
996
945
1029
relative-risk
relative-risk
1
15
4.0
1
1
NIL
HORIZONTAL

TEXTBOX
955
971
1440
1048
Proportion in high risk group CANNOT be changed during the simulation.\n\nThis should really be age-group specific, but probably not required unless using age-specific severity. Influences risk of hospitalisation and whether isolate, but not susceptibility or death.
11
0.0
1

CHOOSER
765
1069
945
1114
scenario-selector
scenario-selector
"off" "unmitigated" "9w45" "9w45shield" "SelfQuarantine" "InformOnly" "9w45sqInform" "atJul13" "Hull#4" "localLockdown" "localHotspot" "adhoc"
0

CHOOSER
765
1114
945
1159
region-selector
region-selector
"off" "UK cases" "75% UK cases" "150% UK cases" "UK admissions" "London admissions"
0

BUTTON
765
1184
947
1217
Set to Null
interventions-off\napply-defaults\nset death-no-bed 0.8\nset distancing-reduction 0.25\nset HR-shield-duration 15\nset trigger-type \"cases\"\nset trigger-level 200\nset intervention-duration 12\nset isolation-efficacy 0.9\nset mild-asymptomatic 0.45\nset SI-isolation-duration 14\nset found-and-isolate 0.4\nset IC-isolation-duration 14\nset when-symptoms-if-I 1\nset max-presymptomatic 3\nset use-age-mixing? false\nset scenario-selector \"off\"\nset region-selector \"off\"\nset randomise? true
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

@#$#@#$#@
# CONTEXT

In the absence of a vaccine or effective treatment, the only way to manage a communicable disease epidemic is to interrupt transmission from infectious people to susceptible people. This involves controlling the ways in which people mix (such as isolating those potentially exposed) and reducing the potential for transmission where they do mix (such as promoting good hand hygiene). This model is intended to help understand the potential impact of combinations of these non-pharmaceutical interventions over time, and the uncertainties associated with estimates of the impact. Full documentation is available as a separate user manual (with example scenarios) and technical reference.

Two processes are represented in the model: transmission and disease progression. These interact through an extended person to person SEIR epidemic model. The disease spreads directly from infectious people to susceptible people, excluding indirect real-world paths such as virus survival on hard surfaces.People start in the susceptible (S) state, change to the exposed state (E) if they come in contact with an infectious person, become infectious (I) some time after they are exposed, and eventually recover (R) and become immune or die. While infectious, they may also require hospital care.

The model starts with 12 people (turtles in NetLogo terminology) on each patch (a cell in the spatial grid). One person starts in the exposed state, and all others are susceptible. Without interventions, each tick (time step, representing one day), any infectious person interacts with all the susceptible people on their patch and, with independent random draws, has the opportunity to expose each of them. To allow the epidemic to spread spatially, some people also move each tick. Short movements are one unit of distance in a random direction, which is likely but not always moving them to a different patch. Long movements are three units of distance.

The policy scenarios modify various aspects of this transmission process, constraining the mixing between infectious and susceptible people. The interventions fall into two broad groups. The first represent social distancing regulations introduced by government such as closing public spaces. The second are individual actions taken by symptomatic people to break transmission chains.

# RUNNING A SCENARIO

The left hand side of the interface contains information about the epidemic, both inputs for the simulation and outputs. The right hand side of the interface has controls for the scenarios to be modelled.

Three sliders are used to control how fast the epidemic spreads by dragging the red marker to the left (to decrease the parameter value) or right. The 'transmission-parameter' is the probability that an infectious person will expose a susceptible person on the same patch excluding any adjustment from the social distancing options. The 'prop-move-short' and 'prop-move-long' sliders control the proportion of people that move each time step. 

Pressing the setup button will initialise the model, for example generating all the agents. The go button is used to start the simulation. The simulation will stop when there are no longer any infectious people, but it can also be paused and restarted by pressing the go button again.

## Social distancing interventions

Unless the trigger is set to 'interactive' the overall epidemic status is used to start social distancing interventions, which apply for a defined period. There are three broad ways of implementing social distancing included in the model.

The first directly reduces contacts or activities, as occurs through closing of schools, work places and public areas. The chooser (drop down box) is used to select the way in which social distancing is implemented in the model (see design above). The slider controls how much reduction in contacts or movement to apply. The 'ByContact' scenario reduces the probability that a contact will result in exposure. This is mathematically equivalent to reducing the number of contacts in the assumptions of a model that uses a mixing matrix, with the same expected number of transmissions. The other methods take advantage of the way in which individuals are represented. If two people independently reduce their activity by some amount, then the actual number of contacts will reduce by more than that amount. This is because each contact depends on both people being present, and the reduction in activity could lead to one being present and the other absent. Conceptually, the 'AllPeople' scenario reduces the activity of every person by the same amount. In contrast, the 'AllOrNone' scenario conceptually reduces the activity of some people to nothing (representing isolation) and has no effect on the activity of all other people.

Separately, high-risk people can shield for a set period that is potentially different than the period that applies to other social distancing policies. If set, those people in the high-risk group are treated as being in isolation.

Finally, the movement scenario changes only the proportion of people moving (short and long). While this does not directly alter the probability of transmission or the number of contacts, it is expected to reduce the effect of those contacts. This is because those people in the infectious state have reduced access to people who have not yet been exposed.

## Responses to symptoms

There are two broad actions that people in the model can take when they become symptomatic. They can isolate themself, and the can inform their contacts so that those contacts have the opportunity to isolate. Whether these actions occur is set by a switch that can be moved between Off and On throughout the epidemic simulation.

## Interpreting the Output

The main output is the plot of the epidemic over time. The plot shows the proportion of the population that are currently infectious or exposed (Prevalence), infectious (Prop Infectious), or newly exposed (Incidence). In addition, the proportion of the population who have ever been infected is reported in the box labelled 'Impact' (referred to as 'final size' in epidemiology). Other outputs concern specific epidemic states such as the number of people newly admitted to hospital (or critical care) and the number currently in hospital. Total and daily deaths are also reported.

# CREDITS AND REFERENCES

Software:&nbsp; JuSt-Social COVID-19 ABM
Copyright: Jennifer Badham (2020)
&nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp;COVID-19 Community Health and Social Care Modelling Team
&nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp;Durham University
Contact: &nbsp; research@criticalconnections.com.au
Design:&nbsp; &nbsp; Jennifer Badham, Peter Barbrook-Johnson, Brian Castellani

While this software is copyrighted, it is released under the terms of the following open source license, which allows it to be used and amended without charge provided appropriate attribution is observed.

	This program is free software: you can redistribute it and/or modify it under the
	terms of the GNU General Public License as published by the Free Software
	Foundation, either version 3 of the License, or (at your option) any later
	version.  This program is distributed in the hope that it will be useful, but
	WITHOUT ANY WARRANTY, without even the implied warranty of MERCHANTABILITY or
	FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
	details.
@#$#@#$#@
default
true
0
Polygon -7500403 true true 150 5 40 250 150 205 260 250

airplane
true
0
Polygon -7500403 true true 150 0 135 15 120 60 120 105 15 165 15 195 120 180 135 240 105 270 120 285 150 270 180 285 210 270 165 240 180 180 285 195 285 165 180 105 180 60 165 15

arrow
true
0
Polygon -7500403 true true 150 0 0 150 105 150 105 293 195 293 195 150 300 150

box
false
0
Polygon -7500403 true true 150 285 285 225 285 75 150 135
Polygon -7500403 true true 150 135 15 75 150 15 285 75
Polygon -7500403 true true 15 75 15 225 150 285 150 135
Line -16777216 false 150 285 150 135
Line -16777216 false 150 135 15 75
Line -16777216 false 150 135 285 75

bug
true
0
Circle -7500403 true true 96 182 108
Circle -7500403 true true 110 127 80
Circle -7500403 true true 110 75 80
Line -7500403 true 150 100 80 30
Line -7500403 true 150 100 220 30

butterfly
true
0
Polygon -7500403 true true 150 165 209 199 225 225 225 255 195 270 165 255 150 240
Polygon -7500403 true true 150 165 89 198 75 225 75 255 105 270 135 255 150 240
Polygon -7500403 true true 139 148 100 105 55 90 25 90 10 105 10 135 25 180 40 195 85 194 139 163
Polygon -7500403 true true 162 150 200 105 245 90 275 90 290 105 290 135 275 180 260 195 215 195 162 165
Polygon -16777216 true false 150 255 135 225 120 150 135 120 150 105 165 120 180 150 165 225
Circle -16777216 true false 135 90 30
Line -16777216 false 150 105 195 60
Line -16777216 false 150 105 105 60

car
false
0
Polygon -7500403 true true 300 180 279 164 261 144 240 135 226 132 213 106 203 84 185 63 159 50 135 50 75 60 0 150 0 165 0 225 300 225 300 180
Circle -16777216 true false 180 180 90
Circle -16777216 true false 30 180 90
Polygon -16777216 true false 162 80 132 78 134 135 209 135 194 105 189 96 180 89
Circle -7500403 true true 47 195 58
Circle -7500403 true true 195 195 58

circle
false
0
Circle -7500403 true true 0 0 300

circle 2
false
0
Circle -7500403 true true 0 0 300
Circle -16777216 true false 30 30 240

cow
false
0
Polygon -7500403 true true 200 193 197 249 179 249 177 196 166 187 140 189 93 191 78 179 72 211 49 209 48 181 37 149 25 120 25 89 45 72 103 84 179 75 198 76 252 64 272 81 293 103 285 121 255 121 242 118 224 167
Polygon -7500403 true true 73 210 86 251 62 249 48 208
Polygon -7500403 true true 25 114 16 195 9 204 23 213 25 200 39 123

cylinder
false
0
Circle -7500403 true true 0 0 300

dot
false
0
Circle -7500403 true true 90 90 120

face happy
false
0
Circle -7500403 true true 8 8 285
Circle -16777216 true false 60 75 60
Circle -16777216 true false 180 75 60
Polygon -16777216 true false 150 255 90 239 62 213 47 191 67 179 90 203 109 218 150 225 192 218 210 203 227 181 251 194 236 217 212 240

face neutral
false
0
Circle -7500403 true true 8 7 285
Circle -16777216 true false 60 75 60
Circle -16777216 true false 180 75 60
Rectangle -16777216 true false 60 195 240 225

face sad
false
0
Circle -7500403 true true 8 8 285
Circle -16777216 true false 60 75 60
Circle -16777216 true false 180 75 60
Polygon -16777216 true false 150 168 90 184 62 210 47 232 67 244 90 220 109 205 150 198 192 205 210 220 227 242 251 229 236 206 212 183

fish
false
0
Polygon -1 true false 44 131 21 87 15 86 0 120 15 150 0 180 13 214 20 212 45 166
Polygon -1 true false 135 195 119 235 95 218 76 210 46 204 60 165
Polygon -1 true false 75 45 83 77 71 103 86 114 166 78 135 60
Polygon -7500403 true true 30 136 151 77 226 81 280 119 292 146 292 160 287 170 270 195 195 210 151 212 30 166
Circle -16777216 true false 215 106 30

flag
false
0
Rectangle -7500403 true true 60 15 75 300
Polygon -7500403 true true 90 150 270 90 90 30
Line -7500403 true 75 135 90 135
Line -7500403 true 75 45 90 45

flower
false
0
Polygon -10899396 true false 135 120 165 165 180 210 180 240 150 300 165 300 195 240 195 195 165 135
Circle -7500403 true true 85 132 38
Circle -7500403 true true 130 147 38
Circle -7500403 true true 192 85 38
Circle -7500403 true true 85 40 38
Circle -7500403 true true 177 40 38
Circle -7500403 true true 177 132 38
Circle -7500403 true true 70 85 38
Circle -7500403 true true 130 25 38
Circle -7500403 true true 96 51 108
Circle -16777216 true false 113 68 74
Polygon -10899396 true false 189 233 219 188 249 173 279 188 234 218
Polygon -10899396 true false 180 255 150 210 105 210 75 240 135 240

house
false
0
Rectangle -7500403 true true 45 120 255 285
Rectangle -16777216 true false 120 210 180 285
Polygon -7500403 true true 15 120 150 15 285 120
Line -16777216 false 30 120 270 120

leaf
false
0
Polygon -7500403 true true 150 210 135 195 120 210 60 210 30 195 60 180 60 165 15 135 30 120 15 105 40 104 45 90 60 90 90 105 105 120 120 120 105 60 120 60 135 30 150 15 165 30 180 60 195 60 180 120 195 120 210 105 240 90 255 90 263 104 285 105 270 120 285 135 240 165 240 180 270 195 240 210 180 210 165 195
Polygon -7500403 true true 135 195 135 240 120 255 105 255 105 285 135 285 165 240 165 195

line
true
0
Line -7500403 true 150 0 150 300

line half
true
0
Line -7500403 true 150 0 150 150

pentagon
false
0
Polygon -7500403 true true 150 15 15 120 60 285 240 285 285 120

person
false
0
Circle -7500403 true true 110 5 80
Polygon -7500403 true true 105 90 120 195 90 285 105 300 135 300 150 225 165 300 195 300 210 285 180 195 195 90
Rectangle -7500403 true true 127 79 172 94
Polygon -7500403 true true 195 90 240 150 225 180 165 105
Polygon -7500403 true true 105 90 60 150 75 180 135 105

plant
false
0
Rectangle -7500403 true true 135 90 165 300
Polygon -7500403 true true 135 255 90 210 45 195 75 255 135 285
Polygon -7500403 true true 165 255 210 210 255 195 225 255 165 285
Polygon -7500403 true true 135 180 90 135 45 120 75 180 135 210
Polygon -7500403 true true 165 180 165 210 225 180 255 120 210 135
Polygon -7500403 true true 135 105 90 60 45 45 75 105 135 135
Polygon -7500403 true true 165 105 165 135 225 105 255 45 210 60
Polygon -7500403 true true 135 90 120 45 150 15 180 45 165 90

sheep
false
15
Circle -1 true true 203 65 88
Circle -1 true true 70 65 162
Circle -1 true true 150 105 120
Polygon -7500403 true false 218 120 240 165 255 165 278 120
Circle -7500403 true false 214 72 67
Rectangle -1 true true 164 223 179 298
Polygon -1 true true 45 285 30 285 30 240 15 195 45 210
Circle -1 true true 3 83 150
Rectangle -1 true true 65 221 80 296
Polygon -1 true true 195 285 210 285 210 240 240 210 195 210
Polygon -7500403 true false 276 85 285 105 302 99 294 83
Polygon -7500403 true false 219 85 210 105 193 99 201 83

square
false
0
Rectangle -7500403 true true 30 30 270 270

square 2
false
0
Rectangle -7500403 true true 30 30 270 270
Rectangle -16777216 true false 60 60 240 240

star
false
0
Polygon -7500403 true true 151 1 185 108 298 108 207 175 242 282 151 216 59 282 94 175 3 108 116 108

target
false
0
Circle -7500403 true true 0 0 300
Circle -16777216 true false 30 30 240
Circle -7500403 true true 60 60 180
Circle -16777216 true false 90 90 120
Circle -7500403 true true 120 120 60

tree
false
0
Circle -7500403 true true 118 3 94
Rectangle -6459832 true false 120 195 180 300
Circle -7500403 true true 65 21 108
Circle -7500403 true true 116 41 127
Circle -7500403 true true 45 90 120
Circle -7500403 true true 104 74 152

triangle
false
0
Polygon -7500403 true true 150 30 15 255 285 255

triangle 2
false
0
Polygon -7500403 true true 150 30 15 255 285 255
Polygon -16777216 true false 151 99 225 223 75 224

truck
false
0
Rectangle -7500403 true true 4 45 195 187
Polygon -7500403 true true 296 193 296 150 259 134 244 104 208 104 207 194
Rectangle -1 true false 195 60 195 105
Polygon -16777216 true false 238 112 252 141 219 141 218 112
Circle -16777216 true false 234 174 42
Rectangle -7500403 true true 181 185 214 194
Circle -16777216 true false 144 174 42
Circle -16777216 true false 24 174 42
Circle -7500403 false true 24 174 42
Circle -7500403 false true 144 174 42
Circle -7500403 false true 234 174 42

turtle
true
0
Polygon -10899396 true false 215 204 240 233 246 254 228 266 215 252 193 210
Polygon -10899396 true false 195 90 225 75 245 75 260 89 269 108 261 124 240 105 225 105 210 105
Polygon -10899396 true false 105 90 75 75 55 75 40 89 31 108 39 124 60 105 75 105 90 105
Polygon -10899396 true false 132 85 134 64 107 51 108 17 150 2 192 18 192 52 169 65 172 87
Polygon -10899396 true false 85 204 60 233 54 254 72 266 85 252 107 210
Polygon -7500403 true true 119 75 179 75 209 101 224 135 220 225 175 261 128 261 81 224 74 135 88 99

wheel
false
0
Circle -7500403 true true 3 3 294
Circle -16777216 true false 30 30 240
Line -7500403 true 150 285 150 15
Line -7500403 true 15 150 285 150
Circle -7500403 true true 120 120 60
Line -7500403 true 216 40 79 269
Line -7500403 true 40 84 269 221
Line -7500403 true 40 216 269 79
Line -7500403 true 84 40 221 269

wolf
false
0
Polygon -16777216 true false 253 133 245 131 245 133
Polygon -7500403 true true 2 194 13 197 30 191 38 193 38 205 20 226 20 257 27 265 38 266 40 260 31 253 31 230 60 206 68 198 75 209 66 228 65 243 82 261 84 268 100 267 103 261 77 239 79 231 100 207 98 196 119 201 143 202 160 195 166 210 172 213 173 238 167 251 160 248 154 265 169 264 178 247 186 240 198 260 200 271 217 271 219 262 207 258 195 230 192 198 210 184 227 164 242 144 259 145 284 151 277 141 293 140 299 134 297 127 273 119 270 105
Polygon -7500403 true true -1 195 14 180 36 166 40 153 53 140 82 131 134 133 159 126 188 115 227 108 236 102 238 98 268 86 269 92 281 87 269 103 269 113

x
false
0
Polygon -7500403 true true 270 75 225 30 30 225 75 270
Polygon -7500403 true true 30 75 75 30 270 225 225 270
@#$#@#$#@
NetLogo 6.1.1
@#$#@#$#@
@#$#@#$#@
@#$#@#$#@
@#$#@#$#@
@#$#@#$#@
default
0.0
-0.2 0 0.0 1.0
0.0 1 1.0 0.0
0.2 0 0.0 1.0
link direction
true
0
Line -7500403 true 150 150 90 180
Line -7500403 true 150 150 210 180
@#$#@#$#@
0
@#$#@#$#@
