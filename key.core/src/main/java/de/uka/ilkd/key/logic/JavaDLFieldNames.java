package de.uka.ilkd.key.logic;


public class JavaDLFieldNames {
    private JavaDLFieldNames() {}

    public static boolean isField(Name name) {
        return isField(name.toString());
    }

    public static boolean isField(String name) {
        return name.contains("::$");
    }

    public static boolean isImplicitField(Name name) {
        return name.toString().contains("::$$");
    }

    public static boolean isImplicit(ProgramElementName name) {
        return name.getProgramName().startsWith("$");
    }

    public static String toJava(String name) {
        return name.replace("::$", "::");
    }

    public static String toJava(Name name) {
        return toJava(name.toString());
    }

    public static String toJavaDL(Name name) {
        return toJavaDL(name.toString());
    }

    public static String toJavaDL(String name) {
        int index = name.indexOf("::");
        assert index > 0;
        return name.substring(0, index) + "::$" + name.substring(index + 2);
    }
}
