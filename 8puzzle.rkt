#lang racket
;-----------------------------------------------------------------------------------
;                 * Puzzle Informed Search Solution
;  Working: 
;     branch-N-Bound, branch-N-Bound+, bestFirst, beamSearch, hillClimbing
;  DFS and BFS probably finish eventually, haven't actually been fully tested
;  implemented Manhattan distance as a heuristic that works
; Use these to test each search:
;(branch-N-Bound+ (list ss) gg)
;(bestFirst (list ss) gg)
;(branch-N-Bound (list ss) gg)
;(beamSearch (list ss) gg)
;(hillClimbing (list ss) gg)
;(bfs (list ss) gg)
;(dfs (list ss) gg)
; change ss to desired start state
;-----------------------------------------------------------------------------------
(define ss '(1 2 3 8 4 5 0 7 6)) ; tested and all searches find the solution
(define ss2 '(2 3 8 1 7 4 6 5 0)) ; tested and (branch-N-Bound, branch-N-Bound+) finds solution nothing else does
(define ss3 '(8 1 0 7 5 3 6 4 2)) ; none so far
(define ss4 '(0 1 3 6 2 7 8 5 4))
(define gg '(1 2 3 8 0 4 7 6 5)) ; the actual solution

;returns size of list
(define myLeng (lambda (x)
                 (cond	
                   ((equal? x '()) 0)
                   (else (+ 1 (myLeng (cdr x)))))))
; appends item to end of list
(define appendToEnd (lambda (item list)
                      (append list item)))

; checks if an element a is in a list lat
(define member? (lambda (a lat)
                  (cond
                    ((null? lat) #f)
                    (else (or (equal? (car lat) a)
                              (member? a (cdr lat)))))))
;should remove paths that loop on themselvesthout loops
; takes a list of paths and returns those wi
(define clearLoops (lambda (list)
                     (cond
                       ((null? list) '())
                       ((member? (car list) (cdr list)) (clearLoops (cdr list)))
                       (else (cons (car list) (clearLoops (cdr list)))))))
;-----------------------------------------------------------------------------------
; returns a zero-based index of the first occurrence of s in los
;  or -1 if there is no occurrence of s in los
(define list-index (lambda (item list)
                     (list-index-helper item list 0)))
;does counting and recursive calls for list-index
(define list-index-helper (lambda (item list cnt)
                  (cond
                   ((null? list) -1)
                   ((eq? item (car list)) cnt)
                   (else (list-index-helper item (cdr list) (+ cnt 1))))))
;-----------------------------------------------------------------------------------
; checks if a path reaches the goal state, goalState must be defined somewhere
(define checkGoal (lambda (goal)
              (lambda (path)
                  (equal? goal (car path))
)))
;-----------------------------------------------------------------------------------
;returns all valid neighbor paths of a single path
(define getNeighbors (lambda (path)
        (define location (list-index 0 (car path)))
        (remove* '(()) ; removes any empty paths
            (clearLoops ; removes looping paths
                (list
                    (try (not (= 0(remainder location 3))) (- location 1) path); try left
                    (try (not (= 2 (remainder location 3))) (+ location 1) path); try righ
                    (try (< 0 (- location 3)) (- location 3) path) ; try up
                    (try (not (> (+ location 3) 8)) (+ location 3) path); try down
        )))))
; check is a t/f value that an expansion is legal
; par1 is location to be swapped with 0
; par2 is rest of path
(define try (lambda (check newLoc path)
              (cond
                (check (cons (getGen newLoc (car path)) path))
                (else '())
          )))
; takes a location of item to be swapped withempty space and the path
; returns the extended path with the two locations swapped
(define getGen (lambda (location state)
                 ;gets item at location in first node of path
                 (swapper 0 (list-ref state location) state)
                  ))
; returns a list the same as list, but with all occurrences of s1 replaced by s2
; all occurrences of s2 replaced by s1.
(define swapper (lambda (s1 s2 slist)
              (cond
                ((equal? slist '()) '()); list empty, return
                ; first element == s1, reutrn s2 & wioth recursive call to swapper
                ((equal? s1 (car slist)) (cons s2 (swapper s1 s2 (cdr slist))))
                ; first element == s2, reutrn s1 & wioth recursive call to swapper
                ((equal? s2 (car slist)) (cons s1 (swapper s1 s2 (cdr slist))))
                ; nothing special, make recursive call
                (else (cons (car slist) (swapper s1 s2 (cdr slist))))
              )))
;------------------------------------------------------------------------------------
; calculates the manhattan distance of a path
(define manhtnDistance (lambda (path)
                         (manhtnDistanceHelper (car path) 0 0))
                         )
; sums up the return of secondHelper on each value of the state and returns that value
; count -> total distance calculated
; currentCheck -> position in list being examined
(define manhtnDistanceHelper (lambda (state currentCheck count)
              (define goalVal (list-ref gg currentCheck))
              (define actVal (list-ref state currentCheck))
              (cond
                 ((= 8 currentCheck) (+ count (secondHelper (list-index actVal gg) (list-index actVal state))))
                 ((equal? goalVal actVal) (manhtnDistanceHelper state (+ 1 currentCheck) count))
                 (else (manhtnDistanceHelper state (+ 1 currentCheck)
                             (+ count (secondHelper (list-index actVal gg) (list-index actVal state)))))
               )))
; takes location of item in goal and in (car path)
; calculates number of moves between those two spots, max 4
(define secondHelper (lambda (goalLoc actLoc)
               (cond 
                 ((< actLoc goalLoc) (+ (quotient (- goalLoc actLoc) 3) (remainder (- goalLoc actLoc) 3)))
                 (else (+ (quotient (- actLoc goalLoc) 3) (remainder (- actLoc goalLoc) 3))))))
;------------------------------------------------------------------------------------
; abstracted function for both running DFS and BFS for this problem
; takes lots of paramaters
;  goalCheck -> function that checks if an item meets the goal
;  extenderfunc -> function that takes (car uncheckedPaths) and (cdr uncheckedPaths)
;                and returns a list with the extension of the first path in the list
;               advanced searches will return a sorted list as needed
;  uncheckedPaths -> list of paths that haven't been checked
;  checkedPaths -> list of paths that have been checked
;  count -> # of paths searched so far
(define generalFSMachine
  (lambda (goalCheck extenderFunc uncheckedPaths visitedStates count)
         (cond
           ((empty? uncheckedPaths) '());nothing else to search, return empty list
           ; first item in uncheckedPaths is the goal, return it
           ((goalCheck (car uncheckedPaths)) (cons (car uncheckedPaths) (cons count '())))                                  
           ; path has already been searched, move to next in uncheckedPaths
           ((member? (caar uncheckedPaths) visitedStates)
                 (generalFSMachine
                  goalCheck extenderFunc (cdr uncheckedPaths) visitedStates count))
           (else
                  ;(display "Searching next: ")
                  ;(display (car uncheckedPaths))
                  ;(newline)
                  ;(display (cdr uncheckedPaths))
                  ;(newline)
                  (generalFSMachine goalCheck extenderFunc (extenderFunc (car uncheckedPaths) (cdr uncheckedPaths))
                       (cons (caar uncheckedPaths) visitedStates) (+ count 1)))
             )))
;-----------------------------------------------------------------------------------------------------------------
; runs best first search on given start node
; DOES NOT WORK I DON'T KNOW WHY
(define bestFirst (lambda (startState goalState)
                    (display "Starting search...")
                    (newline)
                    (define result
                      (generalFSMachine (checkGoal goalState)
                              (bestFirstHelper getNeighbors) (list startState) '() 0))
                    (display (car result))
                    (newline)
                    (display "Paths Searched: ")
                    (display (cadr result))
                    ))
;given a path extender function (extenderFunc)
;returns a function that sorts new extended paths and otherPaths based on manhtnDistance
(define bestFirstHelper (lambda (extenderFunc)
            (lambda (extendPath otherPaths)
             (sort (appendToEnd (extenderFunc extendPath) otherPaths) < #:key manhtnDistance))
              ))
;-----------------------------------------------------------------------------------------------------------------
; runs best first search on given start node
; DOES NOT WORK I DON'T KNOW WHY
(define hillClimbing (lambda (startState goalState)
                    (display "Starting search...")
                    (newline)
                    (define result (generalFSMachine (checkGoal goalState) (bestFirstHelper getNeighbors) (list startState) '() 0))
                    (display (car result))
                    (newline)
                    (display "Paths Searched: ")
                    (display (cadr result))
                    ))
;given a path extender function (extenderFunc)
;returns a function that sorts new extended paths and otherPaths based on manhtnDistance
(define hillClimbingHelper (lambda (extenderFunc)
            (lambda (extendPath otherPaths)
            (append (sort  (extenderFunc extendPath) < #:key manhtnDistance) otherPaths)
              )))
;-----------------------------------------------------------------------------------------------------------------
; runs best first search on given start node
; DOES NOT WORK I DON'T KNOW WHY
(define beamSearch (lambda (startState goalState)
                    (display "Starting search...")
                    (newline)
                    (define result (generalFSMachine (checkGoal goalState) (bestFirstHelper getNeighbors) (list startState) '() 0))
                    (display (car result))
                    (newline)
                    (display "Paths Searched: ")
                    (display (cadr result))
                    ))
;given a path extender function (extenderFunc)
;returns a function that sorts new extended paths and otherPaths based on manhtnDistance
(define beamSearchHelper (lambda (extenderFunc)
            (lambda (extendPath otherPaths) 
              (define new (extenderFunc extendPath))
              ; only push best half of new paths
            (append (beamFilter (sort new < #:key manhtnDistance)
                                (quotient (myLeng new) 2)) otherPaths))
              ))
; returns list of length len leaving out everything else in lop
(define beamFilter (lambda (lop len)
              (cond
                ((equal? 0 len) '())
                (else
                 (cons (car lop) (beamFilter (cdr lop) (- len 1)))))))
;-----------------------------------------------------------------------------------------------------------------
;-----------------------------------------------------------------------------------------------------------------
; runs best first search on given start node
; probably works it'll get there at some point 
(define branch-N-Bound+ (lambda (startState goalState)
                    (display "Starting search...")
                    (newline)
                    (define result (generalFSMachine (checkGoal goalState) (branch-N-Bound+Helper getNeighbors) (list startState) '() 0))
                    (display (car result))
                    (newline)
                    (display "Paths searched: ")
                    (display (cdr result))
                    ))
;given a path extender function (extenderFunc)
;returns a function that sorts new extended paths and otherPaths based on path length and manhtnDistance
(define branch-N-Bound+Helper (lambda (extenderFunc)
            (lambda (extendPath otherPaths)
             (sort (append (extenderFunc extendPath) otherPaths) < #:key branch-N-Bound+HelperHelper))
              ))
; combines the manhtnDistance with the path length
(define branch-N-Bound+HelperHelper (lambda (path)
                      (+ (manhtnDistance path) (myLeng path))
                                        ))
;-----------------------------------------------------------------------------------------------------------------
; runs branch-N-Bound search on given start node
; works
(define branch-N-Bound (lambda (startState goalState)
                    (display "Starting search...")
                    (newline)
                    (define result (generalFSMachine (checkGoal goalState) (branch-N-BoundHelper getNeighbors) (list startState) '() 0))
                    (display (car result))
                    (newline)
                    (display "Nodes Searched: ")
                    (display (cadr result))
                    ))
;given a path extender function (extenderFunc)
;returns a function that sorts new extended paths and otherPaths based on path length
(define branch-N-BoundHelper (lambda (extenderFunc)
            (lambda (extendPath otherPaths)
             (sort (append (extenderFunc extendPath) otherPaths) < #:key myLeng))
              ))
;-----------------------------------------------------------------------------------------------------------------
;makes call to helper BFS function that does the work
; probably stops at some point idk
(define bfs (lambda (startState goalState)
                (display "Running BFS search")
                (newline)
                (define result (generalFSMachine (checkGoal goalState) (bfsHelper getNeighbors) (list startState) '() 0))
                (display "Number of Checked paths: ")
                (display (cadr result))
                (display " Path: ")
                (display (reverse (car result)))
                ))
;returns function that does path extension
(define bfsHelper (lambda (extenderFunc)
                    (lambda (extendPath otherPaths)
                      (appendToEnd (extenderFunc extendPath) otherPaths))))
;-----------------------------------------------------------------------------------------------------------------
;makes call to helper DFS function that does the work
; probably stops at some point who has the time really
(define dfs (lambda (startState goalState)
                (display "Running DFS search")
                (newline)
                (define result (generalFSMachine (checkGoal goalState) (dfsHelper getNeighbors) (list startState) '() 0))
                (display "Number of Checked paths: ")
                (display (cdr result))
                (display " Path: ")
                (display (reverse (car result)))
                ))
;returns function that does path extension
(define dfsHelper (lambda (extenderFunc)
                    (lambda (extendPath otherPaths)
                      (append (extenderFunc extendPath) otherPaths))))
;-----------------------------------------------------------------------------------------------------------------