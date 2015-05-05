example.name = 1 - Least Common Prefix
example.path = Benchmarks/FM12
example.additionalFile.1 = LRS.java
example.additionalFile.2 = LCP.java
example.additionalFile.3 = Lemmas.java
example.additionalFile.4 = SuffixArray.java
example.file = lcp.key

Longest Repeated Substring (LRS) is one of the challenges described in the paper "Implementation-level Verification of Algorithms with KeY" by Daniel Bruns, Wojciech Mostowski, and Mattias Ulbrich; to be published in Software Tools for Technology Transfer (Springer, 2014). It was originally proposed at the verification competition at FM 2012.

Together with a suffix array, LCP can be used to solve interesting text problems, such as finding the longest repeated substring (LRS) in a text.
A suffix array (for a given text) is an array of all suffixes of the text. For the text [7,8,8,6], the suffix array is
  [[7,8,8,6],
     [8,8,6],
       [8,6],
         [6]]

Typically, the suffixes are not stored explicitly as above but represented as pointers into the original text. The suffixes in a suffix array  are sorted in lexicographical order. This way, occurrences of repeated substrings in the original text are neighbors in the suffix array.

For the above, example (assuming pointers are 0-based integers), the sorted suffix array is: [3,0,2,1]
