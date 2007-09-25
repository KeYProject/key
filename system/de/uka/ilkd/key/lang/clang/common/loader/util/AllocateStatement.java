package de.uka.ilkd.key.lang.clang.common.loader.util;

import java.io.OutputStream;
import java.io.PrintStream;
import java.lang.reflect.Method;

import cetus.hir.Expression;
import cetus.hir.Printable;
import cetus.hir.Statement;

public class AllocateStatement extends Statement {
  private static Method class_print_method;

  static
  {
    Class[] params = new Class[2];

    try {
      params[0] = AllocateStatement.class;
      params[1] = OutputStream.class;
      class_print_method = params[0].getMethod("defaultPrint", params);
    } catch (NoSuchMethodException e) {
      throw new InternalError();
    }
  }

  public AllocateStatement(Expression expr)
  {
    object_print_method = class_print_method;
    children.add(expr);
    expr.setParent(this);
  }

  public static void defaultPrint(AllocateStatement stmt, OutputStream stream)
  {
    PrintStream p = new PrintStream(stream);

    p.print("allocate ");
    ((Printable)stmt.children.get(0)).print(stream);
    p.print(";");
  }

  public Expression getExpression()
  {
    return (Expression)children.get(0);
  }

  static public void setClassPrintMethod(Method m)
  {
    class_print_method = m;
  }
}
