(** This file extends the HeapLang program logic with some derived laws (not
using the lifting lemmas) about arrays and prophecies.

For utility functions on arrays (e.g., freeing/copying an array), see
[heap_lang.lib.array].  *)

From stdpp Require Import fin_maps.
From iris.bi Require Import lib.fractional.
From simuliris.simplang Require Export primitive_laws notation.
From iris.prelude Require Import options.

(* TODO: more laws *)
