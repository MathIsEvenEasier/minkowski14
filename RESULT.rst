A unit-distance obstruction in the regular fourteen-gon norm
===========================================================

MathIsEvenEasier, with OpenAI Codex (GPT-6 Astra)
6 October 2026 -- research announcement, external review pending

Statement
---------

Set zeta = exp(pi*i/7) and P = conv{z in C : z^14 = 1}. Let the complex
plane, regarded as a two-dimensional real vector space, carry the
Minkowski functional of P. This is a norm with closed unit ball exactly P.

Theorem. Every map from this plane to four colours has a monochromatic
pair at norm-distance one. Consequently every finite proper unit-distance
colouring uses at least five colours.

The formal conclusion is Minkowski14.at_least_five_colours in
formal/Final.lean. Its only colouring hypothesis is that points at distance
one have distinct colours. The normed space is defined, not assumed.

The norm and its sides
-----------------------

The set of fourteenth roots is finite and stable under negation. Its
convex hull P is compact, convex and balanced. The noncollinear vectors
1 and zeta, together with their negatives, span a diamond inside P;
therefore P absorbs the real plane. Compactness also makes it bounded.
These properties make its gauge a positive-definite seminorm. Closedness
identifies the gauge sublevel set {x : gauge(P,x) <= 1} with P.

For the side joining 1 to zeta, use the real linear functional

  L(z) = Re(z) + Re(conjugate(zeta) * z).

Both endpoints have value 1 + Re(zeta), and every polygon vertex has value
at most this positive constant. Thus L supports P at this side. A convex
combination s(t) = (1-t) + t*zeta with 0 <= t <= 1 belongs to P and attains
that supporting value. It has gauge at most one by membership. It cannot
have gauge less than one, since scaling it into a smaller copy of P would
contradict the supporting-functional bound. Thus gauge(P,s(t)) = 1.
Multiplication by any fourteenth root preserves P, so every rotated side
point zeta^j*s(t) also has gauge one.

These steps are proved in Algebra.lean, Polygon.lean and Facet.lean.
Plane.lean installs the normed additive group and real normed-space
instances and proves that the real dimension is two.

Exact coordinates and edge witnesses
------------------------------------

A coordinate is a six-tuple of integers (a0,...,a5), evaluated as
sum(a_k*zeta^k). The identity

  zeta^6 - zeta^5 + zeta^4 - zeta^3 + zeta^2 - zeta + 1 = 0

makes rotation an exact integer operation. Coordinates.lean proves that
this operation agrees with multiplication by the geometric zeta, and
that coordinate subtraction agrees with complex subtraction.

Define rho = 2*cos(2*pi/7). Lean proves

  rho^3 + rho^2 - 2*rho - 1 = 0,
  1246979603717467 / 10^15 < rho < 1246979603717468 / 10^15.

The root is identified geometrically; it is not an arbitrary root of the
cubic. For each stored graph edge (u,v), an integer witness specifies a
rotation j and a parameter triple (A,B,C), with

  t = A + B*rho + C*rho^2,
  point(u) - point(v) = zeta^j * ((1-t) + t*zeta),
  0 <= t <= 1.

There are 29 parameter triples. Parameters.lean proves their interval
bounds from exact rational inequalities; the generated Geometry modules
check the coordinate equalities using ordinary kernel reduction. Their
edge lists are identified with the graph used in the SAT theorem. The
side lemma therefore proves norm-distance one for all 13,755 listed edges.

The finite obstruction
----------------------

The abstract graph has 1,540 labelled vertices. Each vertex has four
Boolean colour variables. The four-colouring CNF contains:

* 1,540 clauses requiring at least one colour;
* 9,240 clauses requiring at most one colour;
* 55,020 clauses forbidding equal colours across an edge;
* one colour-symmetry clause fixing an anchor to colour zero.

This gives 6,160 variables and 65,801 clauses. Any proper graph colouring
can be relabelled to satisfy the anchor condition. The formal bridge
proves that a proper colouring would satisfy this exact CNF, including
the symmetry normalization and the equality of the encoded clause lists.

The archived LRAT trace gives a refutation of that CNF. The importer reads
literal file paths and builds ordinary Lean proof expressions. Lean's
kernel checks the definitions and theorem declarations. All 42 trace
chunks were rebuilt; the last derives the empty clause. The theorem
MathIsEasy.Minkowski14.FinalGraph.notFourColourable then combines the
semantic bridge and the refutation.

From the graph to the plane
---------------------------

Suppose c were a proper four-colouring of the entire normed plane. Give
abstract vertex v the colour c(point(v)). Every listed graph edge joins
two points at distance one, so the induced graph colouring would be
proper. This contradicts notFourColourable.

This argument needs neither a complete unit-distance edge list nor global
injectivity of the coordinate map. Unit-distance endpoints are already
distinct; possible coincidences of nonadjacent vertices cause no problem
for pulling back a colouring. The Lean proof does not assume injectivity.
Any colouring with n <= 4 colours embeds into four colours, giving the
stated lower bound n >= 5 for every finite proper colouring.

Construction provenance
-----------------------

The archived search began with side parameters
{0, rho-1, rho^2-rho, rho^2-1, 1+rho-rho^2}, their fourteen rotations, and
a sumset of those points. Exact edges were retained and SAT proof cores
were used to reduce the graph to the present 1,540 labelled vertices.
This describes how the witness was found; search completeness and solver
correctness are not premises of the final theorem. The current release
checks the supplied finite object and its refutation directly.

The geometric chain is new in this release. The finite graph, original
CNF/LRAT inputs and earlier logical bridge were retained as source data
and rebuilt after cleaning the importer. Sources and successful compiler
records are matched by hashes. See REPRODUCE.rst and evidence/.

What remains open and relation to prior work
--------------------------------------------

Exoo, Fisher and Ismailescu (2021) prove lower bounds of five for the
regular 8-, 10- and 12-gon norms. Gehér (2023) proves an upper bound of six
for even regular polygons with at most 22 vertices. This includes P14.
Together with the present theorem, that gives

  5 <= chi(R^2,P14) <= 6.

The exact value five or six remains undetermined here. The upper bound is
cited, not part of the Lean development. A bounded literature search did
not locate the same fourteen-gon lower bound in the screened sources;
this does not establish priority. The release seeks mathematical and
prior-work review, not an endorsement of a first-proof claim.

References
----------

1. Geoffrey Exoo, David Fisher and Dan Ismailescu. The chromatic number of
   the Minkowski plane -- the regular polygon case. arXiv:2108.12861 (2021).
   https://arxiv.org/abs/2108.12861
2. Panna Gehér. Note on the chromatic number of Minkowski planes: the regular
   polygon case. arXiv:2301.13695 (2023).
   https://arxiv.org/abs/2301.13695
