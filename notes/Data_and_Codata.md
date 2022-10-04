# Data and Codata

For a detailed introduction to Codata, see _[Codata in
Action][codata-in-action]_ by Paul Downen, Zachary Sullivan, Zena Ariola, Simon
Peyton Jones.

## Data

A **data type** is defined by the following form of declaration

```
data <DatName> : <Kind> where
  [ <DatCon> : <Type> -> <DatName> ]
```

which yields the following definitions

```
// type
axiom <DatName> : <Kind>

// constructors
[ axiom <DatCon> : <Type> -> <DatName> ]

// destructor
axiom match<DatName> : 
  Π A => 
  [ <Type> -> -> A ] ->
  (<DatName> -> A)
```

In other words, a data type is a _sum of products (SoP)_. 
- To construct a term of the data type: for one of the sides, construct the
  product.
- To destruct a term of the data type: for each side, use the product to
  construct `A`.

## Codata

A **codata type** is defined by the following form of declaration

```
codata <CodName> : <Kind> where
  [ <CodDes> : <CodName> -> <Type> ]
```

which yields the following definitions

```
// type
axiom <CodName> : <Kind>

// constructor
axiom make<CodName> :
  [ <CodDes> : <Type> ]
  <CodName>

// destructors
[ axiom <CodDes> : <CodName> -> <Type> ]
```

In other words, a codata type is a _product of sums (PoS)_. 
- To construct a term of the codata type: for each of the sides, construct the
  product.
- To destruct a term of the data type: for one of the sides, use the product to
  construct the goal.

## Conclusion

So, do data types just correspond to sums (i.e. coproducts i.e. variants) and
codata types just correspond to products (i.e. cosums i.e. records)? If that's
true, then they aren't very exotic. But perhaps there is something special about
them when it comes to dependent type theory, for GACTs (generalized algebraic
codata types) in a contrast to GADTs (generalized algebraic data types).

## Resources

- [Codata in Action][codata-in-action]
- [Codata in action, or how to connect Functional Programming and Object Oriented Programming][codata-and-oop]

[codata-in-action]: https://www.microsoft.com/en-us/research/publication/codata-in-action/
[codata-and-oop]: https://www.javiercasas.com/articles/codata-in-action