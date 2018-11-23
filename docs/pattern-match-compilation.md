# Pattern Match Compilation

Emelle uses Luc Maranget's algorithm for pattern match compilation as described
in "Compiling Pattern Matching to Good Decision Trees."

    p ::= C p1 .. pN  -- Constructor pattern
          _           -- Wildcard pattern

    tree ::= Leaf of action
               -- Jump to code
             Switch of int * occurrence * (C -> ?tree) * tree
               -- Switch on constructor of the given occurrence
             Swap
               -- Move something to front of stack

Let there be a matrix of patterns. The algorithm to compile this matrix into a
decision tree is as follows:

- If there are no rows, then produce a fail node.
- If the top row is all wildcards, then produce a leaf node.
- Otherwise, there should exist at least one column with a constructor pattern.
  Choose a such a column. In my implementation, I simply iterate over the first
  row, returning the index of the constructor if one exists.
- If the index isn't the first one, move the column to the front of the matrix.
- For each constructor of the algebraic data type, do the matrix specialization
  operation, then find the decision tree of the specialized matrix.
- Find the default matrix.
- Produce a swap instruction for the index (unless it is the first one) and then
  a switch instruction mapping constructors to specialized matrices or the
  default matrix.

## Matrix specialization:

Remove the rows that begin with a constructor that doesn't match. For the rows
with a matching constructor, pop the pattern off the row and push its children
on the row. For the rows that begin with a wildcard, pop off the wildcard and
push wildcards for each type in the constructor's product type.

This operation is akin to popping a successfully matched scrutinee off the
pattern match stack and pushing its subterms on the stack.

## Default matrix

Remove the rows that start with a constructor. For each row that starts with a
wildcard, pop off the wildcard.

This operation is akin to popping off a scrutinee that failed to match.

I observe that the swap instruction index can be directly stored in the switch
instruction. The swap is entirely a compile-time construct anyway. One keeps
compile-time "occurrences" representing the path to a scrutinee, which get
translated into addresses.

## Binding variables

Associate each pattern with an optional name. Keep a map from names to
occurrences in each row. Upon specialization, insert a mapping from the name for
the popped pattern to its occurrence into the map. When producing a leaf node,
traverse the wildcards and map all remaining names to the corresponding
occurrences and store the resulting map in the leaf node.
