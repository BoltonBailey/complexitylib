/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.Kolmogorov
public import Complexitylib.Metacomplexity.Kolmogorov.Oracle
public import Complexitylib.Metacomplexity.Kolmogorov.Incompressibility
public import Complexitylib.Metacomplexity.ScaledExponent
public import Complexitylib.Metacomplexity.BooleanDependency
public import Complexitylib.Metacomplexity.ListDecoding
public import Complexitylib.Metacomplexity.Hamming
public import Complexitylib.Metacomplexity.StatisticalTest
public import Complexitylib.Metacomplexity.NisanWigderson
public import Complexitylib.Metacomplexity.MINKT
public import Complexitylib.Metacomplexity.MINKT.AuxiliaryUnary
public import Complexitylib.Metacomplexity.MINCKT
public import Complexitylib.Metacomplexity.MCSP
public import Complexitylib.Metacomplexity.MCSP.Shannon
public import Complexitylib.Metacomplexity.MCSP.Raw
public import Complexitylib.Metacomplexity.MCSP.Magnification.Parameters
public import Complexitylib.Metacomplexity.MCSP.Magnification.Frontier

/-!
# Metacomplexity

Public aggregation module for ordinary and oracle-relative machine description
complexity, finite incompressibility, dependency-table codecs, finite list
decoding and Hamming geometry, and the minimum-resource problems built from
them, including canonical MCSP, strict-threshold MINKT, and conditional MinKT
instances. Canonical MCSP also exposes its exact finite Shannon threshold
window, while raw GapMCSP supplies the bare `2^n`-bit input convention used by
hardness magnification. Positive rational exponent scales and the selected
finite magnification parameters make its rounded thresholds and lower-bound
quantifiers explicit.
-/
