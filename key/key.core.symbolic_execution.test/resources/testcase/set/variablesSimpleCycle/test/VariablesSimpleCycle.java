
public class VariablesSimpleCycle {
   private VariablesSimpleCycle next;
   private SomethingElse something;
   private int value;
   
   public int main() {
      next = this;
      something.root = this;
      value = 42;
      return value;
   }
}

class SomethingElse {
   public VariablesSimpleCycle root;
}
