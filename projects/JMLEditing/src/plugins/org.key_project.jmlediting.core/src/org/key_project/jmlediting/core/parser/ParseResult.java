package org.key_project.jmlediting.core.parser;

public class ParseResult<T> {

   final T t;

   final int end;
   
   public ParseResult(T t, int end) {
      super();
      this.t = t;
      this.end = end;
   }
   
   
}
