package a;

public class Helper {
    public static Object out = null;
    public static Object err = null;
    
    public static void err() { }
    
    public static class PublicMemberClass { }
    protected static class ProtectedMemberClass { }
    private static class PrivateMemberClass { }
    static class PackageMemberClass { }
    
    public class NonStaticInnerClass { } // should not be statically imported
    
    public static int publicInt;
    protected static int protectedInt;
    private static int privateInt;
    static int packageInt;
    
    public static void publicFoo() { }
    protected static void protectedFoo() { }
    private static void privateFoo() { }
    static void packageFoo() { }
}