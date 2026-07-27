/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
import Complexitylib.Encoding.Delimit
import Complexitylib.Encoding.Pairing
import Complexitylib.Encoding.Bitstring

/-!
# Encodings

Aggregation module for the machine-independent encoding layer: the shared
self-delimiting block framing and its parsers
(`Complexitylib.Encoding.Delimit`), the pairing codec used by machine inputs
(`Complexitylib.Encoding.Pairing`), and the `BitstringEncoding` typeclass with
instances for common types (`Complexitylib.Encoding.Bitstring`).
-/
