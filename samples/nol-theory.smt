(theory Nol

 :smt-lib-version 2.0
 :written_by "Mihaela Sighireanu"
 :date "2012-07-10"
 :last_modified "2012-10-25"

 :sorts ((Field 2) (SetLoc 0) (SetRef 1) (Space 0))

 :funs  ((emp Space)
         (wsep Space Space :left-assoc)
         (ssep Space Space :left-assoc)
         (par (A) (pto A (SetRef A) Space :left-assoc))
         (tobool Space Bool)
         (tospace Bool Space)
         (par (A B) (ref (Field A B) B (SetRef A)))
         (par (A) (sref (SetRef A) (SetRef A) (SetRef A) :left-assoc))
         (index SetLoc Space Space)
         (par (A) (sloc A SetLoc))
         (unloc SetLoc SetLoc SetLoc :left-assoc)
         (par (A) (inloc A SetLoc Bool))
         (leloc SetLoc SetLoc Bool)
         (eqloc SetLoc SetLoc Bool)
         (par (A) (seloc SetLoc A SetLoc))
        )

 :notes "The generic -- program independent -- signature for the NOLL logic."

 :definition
 "The Noll theory corresponds to signature of the Noll logic
  in which:
  - the sort Field denotes the set of reference fields defined in the program;
    a refrence field is typed by two sorts, thus the arity is 2;
  - the sort SetLoc denotes the set of set of location variables;
  - the sort SetRef denotes the set of typed location variables;
  - the sort Space denotes the set of spatial formulas;

  - for all sp in Space, v a location variable, sr in SetRef, 
             f in Field, a in SetLoc:
      - emp denotes the empty heap space constraint;

      - (wsep sp sp) denotes the weak separating space constraint;

      - (ssep sp sp) denotes the strong separating space constraint;

      - (pto v sr) denotes the points-to space constraint from location v;

      - (toBool sp) transforms a space constraint into a boolean constraint;

      - (toSpace b) transforms a boolean formula into a space formula,
        mainly used to be able to type quantifiers in space formulas;

      - (ref f v) denotes the tuple used in a points-to constraint, where
        f is a reference field which value is v, type is a set;

      - (sref sr sr) denotes the union of sets of tuples used in the points-to
        constraint;

      - (index a sp) bounds a to be the set of locations of sp;

      - (sloc v) denotes the signleton set of locations build on v;

      - (unloc sl sl) denotes the union of two sets;

      - (inloc v sl) denotes the belong to constraint;

      - (eqloc sl sl) denotes the equal constraint between sets of locations;

      - (leloc sl sl) denotes the subset or equal constraint;

      - (seloc sl v) denotes the projection of set sl on the type of v.
 "

)
