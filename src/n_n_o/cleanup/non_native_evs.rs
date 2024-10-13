// Implements two polynomials:
// E_t(y) - polynomial with evaluations 1, t, t^2, ..., t^{m-1}, 0, 0, 0... and its verifier-side evaluation function (can be relatively inefficient, because in practice m is relatively small in all applications)
// E_pt(x, y) - polynomial which contains the limbs of E_pt(x) over non-native field.
// data layout of E_pt(x, y) adheres to the one used in matrix-poly - i.e. every column (values with fixed x and varying y) are layed out in chunks of length m [...][...][...][...]. Padding 0s are not allocated.
