package java.util;

public interface Iterator
{
   public boolean hasNext();
   public /*@nullable@*/ Object next();
   public void remove();
}
