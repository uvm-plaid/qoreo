From Qoreo Require Import Network.
Require Extraction.

Extraction Language OCaml.
Set Extraction Output Directory "extracted".
Extraction "epp.ml" Qoreo.Network.epp.
