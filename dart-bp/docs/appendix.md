# Appendix

## R1CS Constraints

### For refreshing $\rho$ and $s$
Once $\rho, \rho_i, \rho_{i+1}, s_i, s_{i+1}$ are committed in Bulletproof, we get circuit variables for each one of them. Then we enforce multiplication relations among these variables.
```text
These variables are guaranteed to have these values
var_rho = \rho
var_rho_i = \rho_i
var_rho_i_plus_1 = \rho_{i+1}
var_s_i = s_i
var_s_i_plus_1 = s_{i+1}

// Assign circuit variable var_rho_i_plus_1_ to the product of var_rho and var_rho_i
var_rho_i_plus_1_ <- var_rho * var_rho_i

// Assign circuit variable var_s_i_plus_1_ to the product of var_s_i and var_s_i
var_s_i_plus_1_ <- var_s_i * var_s_i

// Enforce that values of var_rho_i_plus_1 and var_rho_i_plus_1_ are same
var_rho_i_plus_1 == var_rho_i_plus_1_

// Enforce that values of var_s_i_plus_1 and var_s_i_plus_1_ are same
var_s_i_plus_1 == var_s_i_plus_1_
```


### For range proof
To prove that a value $v$ is of $n$ bits, i.e. $v \in [0, 2^n-1)$, decompose $v$ into bits and prove that each bit is indeed a bit, i.e. 0 or 1 and the appropriate linear combination of the bits is the original value $v$.
```text
// bits is an array bits of v in little-endian representation.
bits = decompose(v)
// This will be set to different powers of 2 during execution of the loop
m = 1
for bit in bits {
  // Allocate circuit variables a and b and assign them values 1-bit and bit
  a <- 1 - bit
  b <- bit
  
  // Enforce a * b = 0, so one of (a,b) is zero
  a * b == 0
  
  // Enforce that a = 1 - b, so they both are 1 or 0.
  a + (b - 1) == 0
  
  // Add `-bit*2^i` to the linear combination
  v = v - bit * m;
  
  m = m * 2
}

// Enforce v = 0
v == 0
```

------------------------
