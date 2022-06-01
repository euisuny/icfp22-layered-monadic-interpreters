(** * Main module with theorems *)


From ITree Require Export
     Basics.Basics
     Basics.Category
     Basics.CategoryKleisli
     Basics.CategoryKleisliFacts
     Basics.FunctionFacts
     Core.ITreeDefinition
     Core.KTreeFacts
     (* Indexed.FunctionFacts *)
     (* Interp.InterpTFacts *)
     (* Interp.TranslateFacts *)
     (* Interp.HandlerFacts *)
     (* Interp.RecursionFacts *)
     .

Require Export ITree.Eq.
(* Coq sometimes thinks [From ITree Require Export Eq.] means
   [Require Export ITree.Eq.Eq.] *)
