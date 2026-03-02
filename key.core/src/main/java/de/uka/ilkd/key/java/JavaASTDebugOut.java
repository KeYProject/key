package de.uka.ilkd.key.java;

import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.reference.PackageReference;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import org.key_project.logic.Name;
import org.key_project.logic.SyntaxElement;

import java.io.IOException;
import java.io.PrintWriter;
import java.lang.reflect.InvocationTargetException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;

public class JavaASTDebugOut {

    public static final String LOG_DIRECTORY = System.getProperty("key.ast.debug.logdir");


    public static void logCompilationUnit(CompilationUnit compilationUnit) {
        if(LOG_DIRECTORY == null) {
            return;
        }

        try {
            PackageSpecification pack = compilationUnit.packageSpec;
            Path dir;
            if (pack != null) {
                String[] parts = pack.reference.toString().split("\\.");
                dir = Paths.get(LOG_DIRECTORY, parts);
                Files.createDirectories(dir);
            } else {
                dir = Paths.get(LOG_DIRECTORY);
            }

            String fileName = compilationUnit.typeDeclarations.get(0).getName().toString() + ".ast";
            Path file = dir.resolve(fileName);
            writeASTToFile(compilationUnit, file);
        } catch (Exception e) {
            System.err.println("Failed to debug-export Java AST:");
            e.printStackTrace();
        }
    }

    private static void writeASTToFile(CompilationUnit compilationUnit, Path file) throws InvocationTargetException, NoSuchMethodException, IllegalAccessException, IOException {
        try(PrintWriter out = new PrintWriter(Files.newBufferedWriter(file))) {
            writeASTDispatch(compilationUnit, out, 0);
        }
    }

    private static void writeASTDispatch(Object object, PrintWriter out, int indent) throws NoSuchMethodException, InvocationTargetException, IllegalAccessException {
        // ChatGPT
        Class<?> objectClass = object.getClass();
        java.lang.reflect.Method bestMatch = null;

        // Search for the most specific applicable writeAST method
        for (java.lang.reflect.Method method : JavaASTDebugOut.class.getDeclaredMethods()) {
            if (!method.getName().equals("writeAST")) {
                continue;
            }

            Class<?>[] paramTypes = method.getParameterTypes();
            if (paramTypes.length != 3
                || !paramTypes[1].equals(PrintWriter.class)
                || !paramTypes[2].equals(int.class)) {
                continue;
            }

            // Check if the first parameter is assignable from the object's class
            if (paramTypes[0].isAssignableFrom(objectClass)) {
                // If no match yet, or this is more specific than current best match
                if (bestMatch == null
                    || bestMatch.getParameterTypes()[0].isAssignableFrom(paramTypes[0])) {
                    bestMatch = method;
                }
            }
        }

        if (bestMatch == null) {
            throw new NoSuchMethodException(
                "No suitable writeAST method found for " + objectClass.getName());
        }

        bestMatch.invoke(null, object, out, indent);
    }

    private static void writeASTChildren(SyntaxElement se, PrintWriter out, int indent) throws InvocationTargetException, NoSuchMethodException, IllegalAccessException {
        for(int i = 0; i < se.getChildCount(); i++) {
            writeASTDispatch(se.getChild(i), out, indent);
        }
    }

    private static void writeAST(ProgramElementName name, PrintWriter out, int indent) throws InvocationTargetException, NoSuchMethodException, IllegalAccessException {
        writeAST((SourceElement) name, out, indent);
        indent(out, indent + 1);
        out.println("Name: " + name);
    }

    private static void writeAST(ProgramVariable reference, PrintWriter out, int indent) throws InvocationTargetException, NoSuchMethodException, IllegalAccessException {
        writeAST((SourceElement) reference, out, indent);
        indent(out, indent + 1);
        out.println("variable name: " + reference.name());
    }

    private static void writeAST(Literal literal, PrintWriter out, int indent) throws InvocationTargetException, NoSuchMethodException, IllegalAccessException {
        writeAST((SourceElement) literal, out, indent);
        indent(out, indent + 1);
        out.println("literal value: " + literal);
    }

    private static void writeAST(ProgramMethod pm, PrintWriter out, int indent) throws InvocationTargetException, NoSuchMethodException, IllegalAccessException {
        writeAST((SyntaxElement) pm, out, indent);
        indent(out, indent + 1);
        out.println("method name: " + pm.getName());
        writeAST(pm.getMethodDeclaration(), out, indent+1);
    }

    private static void writeAST(SourceElement element, PrintWriter out, int indent) throws NoSuchMethodException, InvocationTargetException, IllegalAccessException {
        indent(out, indent);
        out.println(element.getClass().getSimpleName() + " at " + element.getPositionInfo());
        writeASTChildren(element, out, indent+1);
    }

    private static void writeAST(SyntaxElement element, PrintWriter out, int indent) throws NoSuchMethodException, InvocationTargetException, IllegalAccessException {
        indent(out, indent);
        out.println(element.getClass().getSimpleName());
        writeASTChildren(element, out, indent+1);
    }

    private static void indent(PrintWriter out, int indent) {
        out.print(" ".repeat(indent));
    }
}
