/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import Complexitylib.Encoding.Delimit
public import Complexitylib.Encoding.Pairing
public import Complexitylib.Encoding.Data
public import Complexitylib.Encoding.DataEncode

/-!
# Encodings

Aggregation module for the machine-independent encoding layer: the shared
self-delimiting block framing and its parsers
(`Complexitylib.Encoding.Delimit`), the pairing codec used by machine inputs
(`Complexitylib.Encoding.Pairing`), and the rose-tree `Data` type
(`Complexitylib.Encoding.Data`) together with the `DataEncode` typeclass and its
derived bitstring encoding (`Complexitylib.Encoding.DataEncode`).
-/
