-- Import necessary libraries
import Mathlib

-- Use PUnit which has built-in topology
def ZeroDimModel : Type* := PUnit

-- PUnit automatically gets the discrete topology
instance : DiscreteTopology ZeroDimModel := ⟨fun s => trivial⟩

-- Main variables
variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [ChartedSpace ZeroDimModel M]
