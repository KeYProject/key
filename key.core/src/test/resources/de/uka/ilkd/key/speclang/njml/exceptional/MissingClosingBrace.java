// verbose: true
// broken: true
// msgContains: missing '}'
// position: 8/7

class MissingClosingBrace {    
    /*@ model int modelMethodWithoutClose() {
      @  return 0;
      @*/
}

// Since RBRACE is defined twice in the grammar, this can be reported only like this?!
