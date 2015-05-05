import java.util.Iterator;

public class GenericTests<T extends Cloneable> {
   private T cloneable;
   
   public static <S extends Iterable<String>> void main(S s) {
   }
   
   public static void main(Iterator<java.util.Date> iterator) {
   }
   
   public static <S extends Exception> void main() throws S {
   }
}