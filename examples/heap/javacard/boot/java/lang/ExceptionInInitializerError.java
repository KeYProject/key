package java.lang;

public class ExceptionInInitializerError extends java.lang.LinkageError
{

   public ExceptionInInitializerError() { super(); }
   public ExceptionInInitializerError(java.lang.Throwable throwable) {
      super();
      initCause(throwable);
   }
   public java.lang.Throwable getException();
   public java.lang.Throwable getCause();
}
