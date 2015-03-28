import java.util.Iterator;

public class WildcardTest<T extends java.util.Collection<?>> {
   public static <S extends Iterable<?>> void main(S s) {
   }
   
   public static void mainWildcard(Iterator<? extends String> iterator) {
   }
   
   public static <S extends Exception> void main() throws S {
   }
}