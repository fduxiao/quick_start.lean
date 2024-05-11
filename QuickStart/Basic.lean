/-!
# Basic types and functional programming

## Introduction
The core of modern computer proof assistants is always λ-calculus. This chapter is intended to introduce
some basics about functional programming in lean. In modern (dependent) type theory, the most basic thing
is the `inductive type` and functions into/out of them.
-/


/-!
##
-/

/--
Your own doc string
-/
inductive TrafficLight: Type
