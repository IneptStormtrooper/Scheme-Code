#lang racket
;   
;   Alex Fuerst
;   Cannibals and Missionaries Project
;   representation -> '(3 2 #t) three missionaries and two cannibals on the left side of the river with the boat on the left side of the river
;   
;   Implemented both DFS and BFS with one paramaterized function called generalFSMachine
;   Did not implement anything else because screw sorting in scheme
;   
;   
; command to start the whole shebang:
;(MCdfs checkGoal startState)     ; runs DFS
;(MCbfs checkGoal startState)     ; runs BFS
;(runAllTests) ;-> calls both BFS and DFS as listed above

; 3 missionaries on left side, 3 cannibals on left side, boat on left side
(define startState '((3 3 #t)))
; 3 missionaries on right side, 3 cannibals on right side, boat on right side
(define goalState  '(0 0 #f))

; appends item to end of list
(define appendToEnd (lambda (item list)
                      (append list item)))

; checks if an element a is in a list lat
(define member? (lambda (a lat)
                  (cond
                    ((null? lat) #f)
                    (else (or (equal? (car lat) a)
                              (member? a (cdr lat)))))))

; checks if a node is the goal state, goalState must be defined somewhere
(define checkGoal (lambda (state)
                  (equal? goalState (car state))))

;returns all valid neighbors of a single path
(define getNeighbors (lambda (path)
                       ; get all possible neighbors, then check if they are valid
                       (checkListValid (getAllNeighbors path))))

; returns a list of all the possible new paths from a given path
(define getAllNeighbors (lambda (path)
                     (define firstNode (car path))
                          (cond
                            ;check if on left side of river
                            ((caddr firstNode)
                             (list ;return list of all possible combinations
                             (cons (cons (- (car firstNode) 2) (cons (cadr firstNode) (cons #f '()))) path)
                             (cons (cons (- (car firstNode) 1) (cons (cadr firstNode) (cons #f '()))) path)
                             (cons (cons (car firstNode) (cons (- (cadr firstNode) 2) (cons #f '()))) path)
                             (cons (cons (car firstNode) (cons (- (cadr firstNode) 1) (cons #f '()))) path)
                             (cons (cons (- (car firstNode) 1) (cons (- (cadr firstNode) 1) (cons #f '()))) path)
                             ))
                             ; on right side
                            (else
                             (list ;return list of all possible combinations 
                             (cons (cons (+ (car firstNode) 2) (cons (cadr firstNode) (cons #t '()))) path)
                             (cons (cons (+ (car firstNode) 1) (cons (cadr firstNode) (cons #t '()))) path)
                             (cons (cons (car firstNode) (cons (+ (cadr firstNode) 2) (cons #t '()))) path)
                             (cons (cons (car firstNode) (cons (+ (cadr firstNode) 1) (cons #t '()))) path)
                             (cons (cons (+ (car firstNode) 1) (cons (+ (cadr firstNode) 1) (cons #t '()))) path)
                             ))
)))

;takes in list of nodes and returns those that are
(define checkListValid (lambda (listOfPaths)
                 (cond
                   ((null? listOfPaths) '())
                   ((validNode (car listOfPaths)) (cons (car listOfPaths) (checkListValid (cdr listOfPaths))))
                   (else (checkListValid (cdr listOfPaths)))
                   )))

; checks if a node is valid, returns t/f
(define validNode (lambda (path)
                    (define node (car path))
                    (cond
                      ((and (< (car node) (cadr node)) (not (= 0 (car node)))) #f); more cannibals than missionaries and missionaries != 0
                      ((and (> (car node) (cadr node)) (not (= 3 (car node)))) #f); more missionaries than cannibals and missionaries != 3
                      ((< (car node) 0) #f);negative missionaries
                      ((< (cadr node) 0) #f); negative cannibals
                      ((> (car node) 3) #f); more than 3 missionaries
                      ((> (cadr node) 3) #f); more than 3 missionaries
                      ((member? (car path) (cdr path)) #f); path loops on itself
                      (else #t)); path must be vaild
                    ))

; abstracted function for both running DFS and BFS for this problem
; takes lots of paramaters
;  goalCheck -> function that checks if an item meets the goal
;  appenderFunc -> function that adds the generated paths to the path list
;  extenderfunc -> 
(define generalFSMachine (lambda (goalCheck appenderFunc extenderFunc uncheckedPaths checkedPaths count)
                           (cond
                             ((empty? uncheckedPaths) '());nothing else to search, return empty list
                             ((goalCheck (car uncheckedPaths)) (cons (car uncheckedPaths) (cons count '())))
                                                               ; first item in uncheckedPaths is the goal, return it
                             ((member? (car uncheckedPaths) checkedPaths); path has already been searched, move to next in uncheckedPaths
                                   (generalFSMachine goalCheck appenderFunc (cdr uncheckedPaths) checkedPaths) count)
                             (else
                              (display "Searching next: ")
                              (display (car uncheckedPaths))
                              (newline)
                              (display uncheckedPaths)
                              (newline)
                              (generalFSMachine goalCheck appenderFunc extenderFunc
                                                (appenderFunc (extenderFunc (car uncheckedPaths)) (cdr uncheckedPaths))
                                                (cons (car uncheckedPaths) checkedPaths) (+ 1 count)))
                             )))

;makes call to helper BFS function that does the work
(define MCbfs (lambda (goalFunc startNode)
                (display "Running BFS search")
                (newline)
                (define result (generalFSMachine goalFunc appendToEnd getNeighbors (list startNode) '() 0))
                (display "Number of Checked paths: ")
                (display (cadr result))
                (display " Path: ")
                (display (reverse (car result)))
                ))

;makes call to helper DFS function that does the work
(define MCdfs (lambda (goalFunc startNode)
                (display "Running DFS search")
                (newline)
                (define result (generalFSMachine goalFunc append getNeighbors (list startNode) '() 0))
                (display "Number of Checked paths: ")
                (display (cdr result))
                (display " Path: ")
                (display (reverse (car result)))
                ))

; this function runs DFS and then BFS
(define runAllTests (lambda ()
                        (MCdfs checkGoal startState)     ; runs DFS
                        (MCbfs checkGoal startState)     ; runs BFS
                      ))