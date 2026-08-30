session Performant_Isabelle_ML = Pure +
  theories
    Performant_Isabelle_ML

(*The HOL-level half: runtime symbols (SSymb.thy needs HOL's nat and numerals),
  kept in this repository so that every HOL session above it -- Auto_Sledgehammer,
  Isa-Mini, phi-system -- shares one symbol table and its serializers can name it.*)
session Performant_Isabelle_HOL in "HOL" = HOL +
  sessions
    Performant_Isabelle_ML
  theories
    SSymb