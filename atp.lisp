;Unify Function taken from slides with alteration to handle functions
(defun unify (x y &optional theta)
  (cond ((eql theta 'fail) 'fail)
    ((eql x y) theta)
    ((varp x) (unify-var x y theta))
    ((varp y) (unify-var y x theta))
    ((and (consp x) (consp y))
     (unify (cdr x) (cdr y) (unify (car x) (car y) theta)))
     ((fp x) (unify (first (cdr x)) y))
     ((fp y) (unify (first (cdr y)) x))
    (t 'fail)))
;unify-var function taken directly from slides.
(defun unify-var (var x theta)
  (let ((vb (assoc var theta))
         (xb (assoc x theta)))
    (cond (vb (unify (cdr vb) x theta))
      (xb (unify var (cdr xb) theta))
      ((occurs-p var x theta) 'fail)
      (t (cons (cons var x) theta)))))
;occurs-p taken directly from slides
(defun occurs-p (var x theta)
(cond ((eql var x) t)
  ((and (varp x) (assoc x theta))
    (occurs-p var (cdr (assoc x theta)) theta))
  ((consp x) (or (occurs-p var (car x) theta)
	       (occurs-p var (cdr x) theta)))
  (t nil)))
;removes the not of a clause returning the cdr
(defun eliminate-not (clause)
  (if (equal (first clause) '_NOT) (first (cdr clause)) nil)
  )
;eliminates the or of a clause
(defun eliminate-or (clause)
  (setf returnv (cdr clause))
  returnv
  )
;eliminates all the ors of a kb
(defun eliminate-all-or (base)
  (setf return-list nil)
  (dolist (p base)
    (push (eliminate-or p) return-list)
    )
   return-list)
;unit preference heuristic. However list-length works better so this is not used.
(defun heuristic (clause)
  (setf counter 0)
  (dolist (x clause)
     (cond ((and (listp x)(eliminate-not x))
	      (dolist (z (eliminate-not x))
		 (if (varp z) (incf counter))))
	    ((and (null (eliminate-not x)) (listp x))
	      (dolist (z x)
		(if (varp z)(incf counter))))
      )
    )
counter)
;test to see if a term is a variable
(defun varp ( x )
  ; (print x)
  (if (atom x)
    (if (string= (subseq (string x) 0 1 ) '?)t nil)
  )
)
;tests to see if a term is a function
(defun fp ( x )
  (if (listp x)
    (if (string= (subseq (string (car x )) 0 1) '@ ) t nil))
 
)
;tests to see if a clause contains a function
(defun contains-function (clause)
  (setf bool nil)
  (dolist ( x clause)
     (if (fp  x) (push x bool ))
    
    )
  
   bool)
;substitutes a variable with its binding
(defun substitution (clause theta)
  (setf returnlist nil)
  (dolist (x theta)
    (dolist (y clause) 
      (cond ((eliminate-not y)
	      (setf notless (eliminate-not y))	 
	   
	      (cond ((contains-function notless)
	            (dolist (p (contains-function notless))
		      (setf subs (substitution (list p) theta))
		      (setf notless (substitute (first subs)  p notless :test #'equal)))
		      )
		
		
		)
	      
	  
	      
	      (cond ((find (car x) notless :test #'equal)
		      (setf temp (list '_NOT (substitute (cdr x) (car x) notless)))
		      (if (not (find temp clause :test #'equal))
			(push temp clause))
		      (setf clause (remove y clause :test #'equal))
		      ))
	      )
	(t
	  (setf xclause (copy-list y))
	      (cond ((contains-function y)
	            (dolist (p (contains-function y))
		      (setf subs (substitution (list p) theta))		      
		      (setf xclause (substitute (first subs)  p  y :test #'equal)))
		      (push xclause clause)
		      (setf clause (remove y clause :test #'equal))
		      )
		
		
		)
	  
	  (cond ((find (car x) y :test #'equal)
		  (setf xclause (substitute (cdr x) (car x) xclause))
		  (if (not (find xclause clause :test #'equal))
		    (push xclause clause))
		  (setf clause (remove y clause :test #'equal))
		  )
	    )
	  )
	)
      )
    )
  clause)
;checks to see if two clauses form a goal
(defun goalp (clause1 clause2)

  (cond ((and (eliminate-not (first clause1)) (not (eliminate-not (first clause2))))
	   (cond ((and (= (list-length clause1) 1) (= (list-length clause2) 1)(equal (eliminate-not (first clause1)) (first clause2)))
	    t)))
	  ((and (= (list-length clause1)1) (= (list-length clause2)1)(eliminate-not (first clause2)) (not (eliminate-not (first clause1))))
	    (cond ((and (equal (eliminate-not (first clause2)) (first clause1)))
	    t)))
    )
  )
;checks to see if two clauses are unfiy-able 		
(defun unifyp (clause1 clause2)
  (if (equal (unify clause1 clause2) 'fail) nil t)
  )
;performs the actual unification
(defun unification (clause1 clause2 &optional theta )
  (setf breakloop 0)
  (dolist (p clause1)
    (cond ((eliminate-not p)
	    (dolist (p2 clause2)
	      (cond ((unifyp (eliminate-not p) p2)
		      (setf theta (concatenate 'list (unify (eliminate-not p) p2) theta))
		      (setf clause1 (remove p clause1 :test #'equal))
		      (setf clause2 (remove p2 clause2 :test #'equal)))
			((goalp (list p) (list p2)) (and (< (list-length backup1)1)(< (list-length backup2)1))
		      (setf clause1 (remove p clause1 :test #'equal))
		      (setf clause2 (remove p2 clause2 :test #'equal)))
		  
		  
		  
		  )
		)
	      )
	    
      (t
	(dolist (p2 clause2)
	  (cond ((unifyp p (eliminate-not p2))
		  (setf theta (concatenate 'list (unify p (eliminate-not p2)) theta))
		  (setf clause1 (remove p clause1 :test #'equal))
		  (setf clause2 (remove p2 clause2 :test #'equal)))
	    	((goalp (list p) (list p2)) (and (< (list-length backup1)1)(< (list-length backup2)1))
		      (setf clause1 (remove p clause1 :test #'equal))
		      (setf clause2 (remove p2 clause2 :test #'equal)))
		  
		  
		  
		  )
	    )
	  )
	)
      
    (if (> breakloop 0) (return)))
  (setf returnval (concatenate 'list clause1 clause2))
  (if (null returnval) nil
    (if (null theta )(concatenate 'list (list returnval) (list theta)) (concatenate 'list (list  (substitution returnval theta)) (list theta)))))
;converts a sorted list to a list of nodes
(defun convert-to-nodes (sortedlist)
  (setf nodelist nil)
  (dolist (x sortedlist)
    (push (make-node
	    :state x
	    :sortedlist (list sortedlist)) nodelist))
  (setf nodelist (sort nodelist #'nodecompare))
  nodelist)
;eliminates repeats NOT WORKING
(defun eliminate-repeats (result)
  (dolist (x result)
    (dolist (y result)
      (if (equal x y)
	(setf result (remove y result :test #'equal)))))
  result)
;checks to see if there is more than one way to resolve a pair of clauses
(defun conflictp (clause1 clause2)
  (setf counter 0)
  (dolist (p clause1)
    (cond ((eliminate-not p)
	    (dolist (p2 clause2)
	      (if (unifyp (eliminate-not p) p2) (incf counter))
	      )
	    )
      (t
	(dolist (p2 clause2)
	  (cond ((unifyp p (eliminate-not p2))
		   (if (unifyp p (eliminate-not p2)) (incf counter))
		  )
	    )
	  )
	)
    )
   )
  counter
  )
;if there is conflict, unifies all possibilities
 (defun resolve-conflicts (clause1 clause2)
   (setf copy1 (concatenate 'list clause1 clause2))
   (setf copy2 (concatenate 'list clause1 clause2))
   (setf doubles nil)
   (dolist (p copy1)
     (dolist (p2 copy1)
       (cond ((eliminate-not p)
	       (cond ((eliminate-not p2)
		       (cond ((and (equal (first (eliminate-not p)) (first (eliminate-not p2)))
				(not (equal p p2)))
			       (setf copy1 (remove p copy1 :test #'equal))
       			       (setf copy1 (remove p2 copy1 :test #'equal))
			       )))))
	 ((and (not (equal p p2 )) (equal (first p ) (first p2)) (not (null p))(not (null p2)))
	    (setf copy1 (remove p copy1 :test #'equal))
	    (setf copy1 (remove p2 copy1 :test #'equal))))))
  (setf repeats (set-difference copy2 copy1))
  (dolist (x repeats)
    (push (concatenate 'list (list clause1) (list clause2) (unification (concatenate 'list (list x) (set-difference repeats (list x))) copy1)) doubles))
   doubles)
;node structure
(defstruct node
(state nil)
(parent1 nil)
(parent2 nil)
(theta nil)
(action nil)
(sortedlist nil)
(path-cost 0)
(depth 0))
;searches all nodes for a goal
(defun goalsearch (nodelist)
  (setf bool nil)
  (dolist (x nodelist)
    (if (goalp (node-parent1 x) (node-parent2 x)) (setf bool x))
    (if (not (null bool)) (return))
    
    )
  bool)
;creates the successors to a nodestate
(defun successor (nodestate nlist)
  (setf bool 1)
  (setf quadruples nil)
  (dolist (p   nlist)
    (setf temp-nlist (copy-list nlist))
    (setf temp (unification nodestate p))
    (cond 
      ((goalp  nodestate  p)

	  (setf quadruples nil)
          (push (concatenate 'list (list nodestate) (list p) nil nil) quadruples)
	  (incf bool)
          )
       ((and (> (conflictp p nodestate ) 1) (not (null temp)) (not (null (first temp))))
       (setf conflicts (resolve-conflicts nodestate p))
        (dolist (p2 conflicts)
	  (cond ((and (usedp (caddr p2) nlist) ) 
	   (setf temp2 (concatenate 'list temp-nlist (list (caddr p2))))
          (setf temp2 (sort temp2 #'compare))

         (push (concatenate 'list p2 (list temp2)) quadruples);)
        ))))      
      ((and (not (null temp)) (not (null (first temp)))(= (conflictp nodestate p)1)(usedp (first temp) nlist)  
	 (or (or (< (list-length (first temp)) (list-length p)) (> (heuristic (first temp)) 0)) (or (< (list-length (first temp)) (list-length nodestate)) (> (heuristic (first temp)) 0))   ))
	   (push (first temp) temp-nlist)
	    (setf temp-nlist (sort temp-nlist #'compare))
	    (push (concatenate 'list (list nodestate) (list p) temp (list temp-nlist) ) quadruples) 
	    )
      
      ))
   quadruples)
;checks if two nodes are the same
(defun samep (node1 node2)
  (if (and (equal (node-parent1 node1) (node-parent1 node2)) (equal (node-parent2 node1) (node-parent2 node2))
	(equal (node-state node1) (node-state node1))) t nil)  
  )
;checks if a resolvent is in a list		   
(defun usedp (nodestate sortedlist )
   (if (find nodestate sortedlist :test #'equal) nil t)
  
   )
;runs atp
(defun atp (kb nq)
  (pop kb) (pop nq)
  (setf sortedlist (eliminate-all-or (concatenate 'list nq kb)))
  (setf temp (sort sortedlist #'compare))
  (setf node-list (convert-to-nodes temp))
  (setf node-list (sort node-list #'nodecompare))
 ( tree-search node-list)
)
;searches the nodes
 (defun tree-search ( nodelist)
     (cond (( goalsearch nodelist ) (print (list-length nodelist)) (print-action (node-action (goalsearch nodelist))))
       ((= (list-length nodelist) 0) (print "No Solution Found"))
       (t
	   (setf node (pop nodelist))
	 (setf nodelist (sort (concatenate 'list nodelist (expand-nodes #'successor node)) #'nodecompare))
 	 (tree-search nodelist)	 
	 ))
  )
;formats the printing
(defun print-action (nlist)
  (dolist (x nlist)
    (print "(" )
    (print (first (car x)))
    (print (first (cadr x)))
    (print (first (caddr x)))
    (print (first (cadddr x)))
    (print ")") 
    
    
    )
  )
;expands nodes via successor
(defun expand-nodes (successor node)
  (setf quadruples (funcall successor (node-state node) (first (node-sortedlist node))))
  (setf bool 0)
  (setf nodelist nil)
  (setf winner nil)
  (dolist (p quadruples)
    (cond ((goalp (car p) (cadr p))
	 
        (push (make-node 
      	      :parent1 (car p)
      	      :parent2 (cadr p)
      	      :state (caddr p)
      	      :sortedlist  (last p)
      	      :theta (cadddr p)
		:action (concatenate 'list (node-action node) (list (list (list (car p)) (list (cadr p)) (list (caddr p)) (list (cadddr p)))))
	      :path-cost (1+ (node-path-cost node))

      	      )
       winner)
          (setf quadruples nil)
          (return))
      (t
	(push (make-node 
		      :parent1 (car p)
		      :parent2 (cadr p)
		      :state (caddr p)
		      :sortedlist  (last p)
		      :theta (cadddr p)
		      :action (concatenate 'list (node-action node)(list (list (list (car p)) (list (cadr p)) (list (caddr p)) (list (cadddr p)))))
		      :path-cost (1+ (node-path-cost node))
		      )
      nodelist))
	
	    
    ))
   (if (not (null winner)) winner nodelist))
;KB1. Example given via email
(defparameter kb '(_AND ;Remember to fix this!!1111
		     (_OR (WS ?x) (SD ?x))    ;Every member of the CRC is either a scuba diver or a water skier or both
		     (_OR (_NOT (SD ?y)) (_NOT (Like ?y Waves)))  ;No scuba diver likes big waves, and all water skiers like warm water.
		     (_OR (_NOT (WS ?z)) (Like ?z Warm))   ;Laura dislikes whatever Jacob likes, and likes whatever Jacob dislikes.
		     (_OR   (_NOT (Like Laura ?w))(_NOT (Like Jacob ?w)))
		     (_OR (Like Jacob ?w) (Like Laura ?w))
		     (_OR (Like Jacob Warm))  ;Jacob likes warm water and big waves.
		     (_OR (Like Jacob Waves)))
  
)
;NQ1 example given via email
(defparameter nq '(_AND ;also fix this11!!! 
(_OR (_NOT (SD ?v)) (WS ?v))))
;Kb2 example with functions given via email
(defparameter kb2 '(_AND ;Remembr to fix this!!1111
		     (_OR (_Not (Columbia ?x)) (isCourse (@sf ?x))) ;If someone is not at columbia there is a course elsewhere with the student enrolled
		     (_OR (_NOT (Columbia ?x)) (TakeCourse ?x  (@sf ?x)))  ;If someone does not go to columbia  they take a course elsewhere
		     (_OR (Columbia John)) ; John goes to Columbia
		    )
)
;nq2
(defparameter nq2 '(_AND ;also fix this11!!! 
(_OR (_NOT (isCourse ?y)) (_NOT (TakeCourse John ?y)))))
;kb3 taken from slidees
(defparameter kb3 '(_AND ;Remember to fix this!!1111
		     (_OR (_NOT (american ?x)) (_NOT ( weapon ?y))(_NOT (sells ?x ?y ?z)) (_NOT (hostile ?z)) (criminal ?x));it is a crime for an American to sell weapons to a hostile nation
		     (_OR (owns foo mi)) ;Foo has some missles
		     (_OR (missle mi)) ;Foo has some missles
		     (_OR (_NOT ( missle ?x)) (_NOT (owns Foo ?x)) (sells west ?x foo));• all of Foo’s missles were sold to it by Colonel West
		     (_OR (_NOT (missle ?x)) (weapon ?x))	;missles are weapons
		     (_OR (_NOT (enemy ?x america)) (hostile ?x)) ;an enemy of America is considered hostile
		     (_OR (american west)) ;West is American
		     (_OR (enemy foo america)) ;Foo is an enemy of America
		
		    
))
;corresponding nq
(defparameter nq3 '(_AND ;also fix this11!!! 
(_OR (_NOT (criminal west)))))
;extra example found online. short on time so looks for examples.
(defparameter kb4 '( _AND
	( _OR (_NOT (Pass ?x History)) (_NOT (Win ?x lottery)) (Happy ?x)) ;
	( _OR (_NOT (Study ?x)) (Pass (?y ?z)))
	(_OR (_NOT (Lucky ?w)) (Pass ?w ?z))
        (_OR (_NOT (Study John))) ;john did not study
	(_OR (_NOT (Lucky ?v)) (Win ?v lottery)) ; winning the lottery
	(_OR (Lucky John))
		    
		     
		     
		     
		))
;corresponding nq
(defparameter nq4 '(AND
  (_OR (_NOT (Happy John)))))
;more online examples below:
(defparameter kb5 '( _AND
	( _OR (_NOT (dog ?z)) (animal ?z))
	(_OR (_NOT (animal ?y)) (die ?y))
	(_OR (dog fido))

	))	
(defparameter nq5 '(AND
  (_OR (_NOT (die fido)))))
(defparameter kb6 '( _AND
		     ( _OR (Poor ?x) (_NOT (Smart ?x )) (Happy ?x)) ;someone is either notsmart and poor and happy or the reverse
	( _OR (_NOT (Read ?y)) (Smart ?y )) ;someone who
	(_OR (Read John)) ; john reads
	(_OR (_NOT (Poor John))); john is not poor
		     (_OR (_NOT (Happy ?z)) (Exciting ?z )))) ;someone is either not happy or exciting

(defparameter nq6 
  '(AND(_OR (_NOT (Exciting ?w))))) 

;compare function for the lists within eachnodes which pushes the single unit/non variable clauses out first
(defun compare (x y )
  (if (< (list-length x) (list-length y)) x)
)
;length heuristic that places the more complicated clauses first(makes the resolutions a lot faster i found.)
(defun nodecompare (node1 node2)
  ;(if (> (+  (heuristic (node-state node1)) (node-path-cost node1)) (+  (heuristic (node-state node2)) (node-path-cost node2)))  t)
   (if (>= (+  (list-length (node-state node1)) (node-path-cost node1)) (+  (list-length (node-state node2)) (node-path-cost node2)))  t)
  )






(atp kb6 nq6)
;(atp kb2 nq2)


