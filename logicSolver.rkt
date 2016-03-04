#lang racket
;          Theorem Prover 
;  tests everything against everything else to create new steps 
;  Accomplishes up to A level, numbering steps and which ones they came from
;
;   This is the format to run the program:
;
;     (runner rain-axioms rain-contra)
;
;   If it does not reach a contradictory conclusion then it will state that and print the axioms at that point
;   If it is solvable it will do the same but state that it did work
;
; Representation:
; single axiom -> (#t x)
; negation of axiom -> (#f x)
; single hypothesis -> ( ((#t x) (#f x)) (1))
; first item is the list of axioms
; second is a list of the number in which it was added to proof
; is just a list of axioms
; all hypotheses -> list of them ( (((#t x) (#f x)) (1)) (((#t a) (#f x)) (2)) )


(define rain-axioms '((((#f r) (#t u)) (1)) (((#f u) (#f w)) (2)) (((#t r) (#f w)) (3))) )
(define rain-contra '((((#t w)) (4))) )

(define test1-axioms '((((#f p) (#t q)) (1)) (((#f p) (#t r)) (2))))
(define test1-contra '((((#t p)) (3)) (((#f q) (#f r)) (4))))
;------------------------------------------------------------------------------------------
;      Simple stuff
;------------------------------------------------------------------------------------------
; returns size of list
(define myLeng (lambda (x)
                 (cond	
                   ((equal? x '()) 0)
                   (else (+ 1 (myLeng (cdr x)))))))
; appends item to end of list
(define appendToEnd (lambda (item list)
                      (append list item)))

; checks if an element (atom) is in a list (lat)
; does not check sublists
(define member? (lambda (atom lat)
                  (cond
                    ((null? lat) #f)
                    ((equal? atom (car lat)) #t)
                    (else (member? atom (cdr lat))))))
;------------------------------------------------------------------------------------------
; Things specifically for this project
;------------------------------------------------------------------------------------------
; function that returns the hypotheses number of an item
(define getValue (lambda (item)
                   (caadr item)))
; like member? but works with hypotheses that have numbers at the end
; checks if a hypotheses is in a given list even if they have different numbers
(define axiomMember? (lambda (atom lat)
                  (cond
                    ((null? lat) #f)
                    ((null? (car atom))
                        (cond
                          ((null? (caar lat)) #t)
                          (else
                             (axiomMember? atom (cdr lat)))))
                    ((equal? (car atom) (caar lat)) #t)
                    (else (axiomMember? atom (cdr lat))))))
;------------------------------------------------------------------------------------------
; removes any duplicate items in lst and returns it without them
; works properly for hypotheses with numbers
(define removeDups (lambda (lst)
                     (cond
                     ((null? lst) '())
                     ((axiomMember? (car lst) (cdr lst))
                         (cons (car lst) (removeDups (removeDupsHelper (car lst) (cdr lst)))))
                     (else (cons (car lst) (removeDups (cdr lst)))
                      ))))
; does the work for removeDups and removeDupsSimple
; compares an atom to a list to see if any match
(define removeDupsHelper (lambda (atm lst)
                    (cond
                      ((null? lst) '())
                      ((equal? (car atm) (caar lst)) (removeDupsHelper atm (cdr lst)))
                      (else (cons (car lst) (removeDupsHelper atm (cdr lst)))))))
; removes any duplicate items in lst and returns it without them
; works properly for hypotheses without numbers
(define removeDupsSimple (lambda (lst)
                      (cond
                     ((null? lst) '())
                     ((member? (car lst) (cdr lst))
                         (cons (car lst) (removeDupsSimple (removeDupsHelper (car lst) (cdr lst)))))
                     (else (cons (car lst) (removeDupsSimple (cdr lst)))
                           ))))
;------------------------------------------------------------------------------------------

; perform resolution on two full hypotheses (with numbers)
; assumes that the two are legally able to be calculated
(define resolutionCalculator (lambda (hyp1 hyp2 count)
           (list (clearOps (removeDupsSimple (append (car hyp1) (car hyp2))))
                                (list count (caadr hyp1) (caadr hyp2)))
                     ))
; removes any opposite pairs in lst
; works properly for hypotheses with numbers
(define clearOps (lambda (lst)
                   (cond
                     ((null? lst) '())
                     ((hasOpp? (car lst) (cdr lst)) (clearOpsHelper (car lst) (cdr lst)))
                     (else (cons (car lst) (clearOps (cdr lst))))
                    )))
; compares single item (atm) against whole list (lst)
(define clearOpsHelper (lambda (atm lst)
                         (cond
                           ((null? lst) '())
                           ((opposites? atm (car lst)) (cdr lst))
                           (else (cons (car lst) (clearOpsHelper atm (cdr lst))))
                           )))
; returns t/f it atm has an opposite in lst
(define hasOpp? (lambda (atm lst)
                  (cond
                    ((null? lst) #f)
                    ((opposites? atm (car lst)) #t)
                    (else (hasOpp? atm (cdr lst))))))

;------------------------------------------------------------------------------------------
; returns t/f if two hypotheses (with numbers) are resolvable
(define resolvable? (lambda (cond1 cond2)
                      (resvAct (car cond1) (car cond2))))
; takes two hypotheses without numbers at end and checks if they can be resolved
(define resvAct (lambda (cond1 cond2)
                       (cond
                        ((null? cond1) #f)
                        ((resolvable?Helper (car cond1) cond2) #t)
                        (else
                         (resvAct (cdr cond1) cond2)
                      ))))
; compares an atom to a whole list to see if any of them are resolvable on
(define resolvable?Helper (lambda (atm lst)
                            (cond
                              ((null? lst) #f)
                              ((opposites? atm (car lst)) #t)
                              (else
                                 (resolvable?Helper atm (cdr lst))))))
; takes two axioms and returns true if they are opposites
; checks if they have the same value but different signs
(define opposites? (lambda (axiom1 axiom2)
       (and (equal? (cdr axiom1) (cdr axiom2)) (not (equal? (car axiom1) (car axiom2)))
                     )))
;------------------------------------------------------------------------------------------
; given a list of hypotheses it will try to call resolution on all of them to each others
; returnsthe newly created items and the original list of stuff put in in order
; removes any duplicates in list
; count is the next number to be added
(define resolutionIt (lambda (checkList count)
                       (define stuff (resolutionItHelper checkList '() '() count))
                       (cond
                         ((null? stuff) '())
                         (else
                      (removeDups (sort (append checkList stuff) < #:key getValue)))
                       )))
; calls resolution on each pair given in notChecked
; notChecked -> list of hypotheses that haven't been expanded
; checked -> hypotheses that have been checked
; calculated -> hypotheses that have been generated
(define resolutionItHelper (lambda (notChecked checked calculated count)
             (cond
                 ((null? notChecked) calculated)
                 (else;try not to look at this
                    (resolutionItHelper (cdr notChecked) (append checked (list (car notChecked)))
                          (append (secondHelper (car notChecked) (append checked (cdr notChecked)) count) calculated)
                             (+ count (myLeng (secondHelper (car notChecked) (append checked (cdr notChecked)) count))))
             ))))
; returns a list of resolution of everything in list wih item
(define secondHelper (lambda (item lst count)
         (cond
            ((null? lst) '())
            (else
               (cond; check if first item can be resolver, if so do it
                 ((resolvable? item (car lst))
                   (cons (resolutionCalculator item (car lst) (+ 1 count)) (secondHelper item (cdr lst) (+ 1 count))))
               (else
                   (secondHelper item (cdr lst) count)))
          ))))
;------------------------------------------------------------------------------------------
; runs everything and prints goal path if goal is reached, otherwise states that it is unreachable
; takes hypotheses and conclusions in 2 vars
; these are combined into one list b/c reasons
(define runner (lambda (knownHyps conc)
                 (runnerMain (append knownHyps conc) (myLeng (append knownHyps conc)))
                 ))
; takes a list of hypotheses and the count of how many there are
; loops trying to generate new hypotheses and reaches () or doesn't make any more 
(define runnerMain (lambda (knownHyps count)
                 (define newStuff (resolutionIt knownHyps count))
                 (cond
                   ((equal? newStuff knownHyps) (display "Can't compute") (newline) (printList newStuff))
                   ((checkGoal newStuff) (display "Goal Reached!") (newline) (printList newStuff)); reached contradiction
                   (else
                   (runnerMain newStuff (myLeng newStuff))))
                     ))
;------------------------------------------------------------------------------------------
; nicely prints the list with line nums and where they were generated from
(define printList (lambda (lst)
                    (cond
                      ((null? lst) (newline) (display "_________________________"))
                      (else
                       (display (caar lst))
                       (display " ")
                       (display "Line: ")
                       (display (caadar lst))
                       (display "  Generated from: ")
                       (display (cdadar lst))
                       (newline)
                       (printList (cdr lst))))))
; takes a list lst of hypotheses and sees if any of them contain '()
(define checkGoal (lambda (lst)
                    (cond
                      ((null? lst) #f)
                      ((equal? '() (caar lst)) #t)
                      (else
                       (checkGoal (cdr lst))))))