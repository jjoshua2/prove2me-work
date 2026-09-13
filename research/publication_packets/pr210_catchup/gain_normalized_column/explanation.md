# Gain-normalized inverse-column bound

The denominator lower bound makes its absolute value positive. After rewriting the absolute value of the quotient, cross-multiplication is legitimate because both the denominator magnitude and `eta` are positive. The transport inequality contributes the upper bound on `eta * |x|`; the gap inequality contributes the lower bound on `Gamma * |denominator|`. Combining them gives `|x / denominator| ≤ Gamma / eta`. This is the scalar normalization step used after graph structure supplies the path-gain and cycle-gap certificates.
