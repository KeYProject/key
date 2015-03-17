package org.key_project.stubby.core.template;

import java.util.List;

import org.key_project.stubby.model.dependencymodel.AbstractType;
import org.key_project.stubby.model.dependencymodel.Field;
import org.key_project.stubby.model.dependencymodel.Method;
import org.key_project.stubby.model.dependencymodel.Type;
import org.key_project.stubby.model.dependencymodel.TypeVariable;
import org.key_project.stubby.model.dependencymodel.Visibility;
import org.key_project.util.java.StringUtil;

/**
 * Template to generate a Java file containing stubs.
 * @author Martin Hentschel
 */
public class TypeTemplate {
   /**
    * The new line separator.
    */
   protected static String nl;

   /**
    * Creates a new {@link TypeTemplate}.
    * @param lineSeparator The line separator to use.
    * @return The created {@link TypeTemplate}.
    */
   public static synchronized TypeTemplate create(String lineSeparator) {
      nl = lineSeparator;
      TypeTemplate result = new TypeTemplate();
      nl = null;
      return result;
   }

   /**
    * The new line separator to use.
    */
   public final String NL = nl == null ? (StringUtil.NEW_LINE) : nl;

   /**
    * Generates the Java file content.
    * @param argument The argument.
    * @return The created Java file.
    */
   public String generate(Object argument) {
      final StringBuffer sb = new StringBuffer();
      Type type = (Type) argument;
      if (type.getPackage() != null) {
         sb.append("package ");
         sb.append(type.getPackage());
         sb.append(";" + NL + NL);
      }
      appendType(type, sb, 0);
      return sb.toString();
   }
   
   protected void appendType(Type type, StringBuffer sb, int level) {
      final String INDENT = StringUtil.createLine(" ", level * 3);
      // Append type declaration
      sb.append(INDENT + "/**" + NL + INDENT + " * @generated" + NL + INDENT + " */" + NL);
      sb.append(INDENT + type.getVisibility().toJavaKeyword());
      if (!Visibility.DEFAULT.equals(type.getVisibility())) {
         sb.append(" ");
      }
      if (type.isFinal()) {
         sb.append("final ");
      }
      if (type.isStatic()) {
         sb.append("static ");
      }
      if (type.isAbstract()) {
         sb.append("abstract ");
      }
      sb.append(type.getKind().toJavaKindKeyword());
      sb.append(" ");
      sb.append(type.getSimpleName());
      if (!type.getTypeVariables().isEmpty()) {
         sb.append("<");
         boolean afterFirst = false;
         for (TypeVariable var : type.getTypeVariables()) {
            if (afterFirst) {
               sb.append(", ");
            }
            else {
               afterFirst = true;
            }
            sb.append(var.getName());
            sb.append(" extends ");
            sb.append(var.getType().getName());
         }
         sb.append(">");
      }
      if (!type.getExtends().isEmpty()) {
         sb.append(" extends ");
         boolean afterFirst = false;
         for (AbstractType extendType : type.getExtends()) {
            if (afterFirst) {
               sb.append(", ");
            }
            else {
               afterFirst = true;
            }
            sb.append(extendType.getName());
         }
      }
      if (!type.getImplements().isEmpty()) {
         sb.append(" implements ");
         boolean afterFirst = false;
         for (AbstractType extendType : type.getImplements()) {
            if (afterFirst) {
               sb.append(", ");
            }
            else {
               afterFirst = true;
            }
            sb.append(extendType.getName());
         }
      }
      sb.append(" {" + NL);
      // Append fields
      boolean afterFirstMember = false;
      List<Field> allFields = type.getFields();
      for (Field stubField : allFields) {
         afterFirstMember = appendNewMemberSeparator(afterFirstMember, sb);
         appendField(stubField, sb, level + 1);
      }
      // Append methods
      List<Method> allMethods = type.getMethods();
      for (Method method : allMethods) {
         afterFirstMember = appendNewMemberSeparator(afterFirstMember, sb);
         appendMethod(method, sb, level + 1);
      }
      // Append inner types
      for (Type innerType : type.getInnerTypes()) {
         afterFirstMember = appendNewMemberSeparator(afterFirstMember, sb);
         appendType(innerType, sb, level + 1);
      }
      if (afterFirstMember) {
         sb.append(NL);
      }
      sb.append(INDENT +"}");
   }

   protected void appendMethod(Method method, StringBuffer sb, int level) {
      final String INDENT = StringUtil.createLine(" ", level * 3);
      sb.append(INDENT + "/*@ normal_behavior" + NL);
      sb.append(INDENT + "  @ requires true;" + NL);
      sb.append(INDENT + "  @ ensures true;" + NL);
      sb.append(INDENT + "  @ assignable \\everything;" + NL);
      sb.append(INDENT + "  @*/" + NL);
      sb.append(INDENT + "/**" + NL);
      sb.append(INDENT + " * @generated" + NL);
      sb.append(INDENT + " */" + NL);
      sb.append(INDENT + method.getVisibility().toJavaKeyword() + " ");
      if (method.isAbstract()) {
         sb.append("abstract ");
      }
      if (method.isStatic()) {
         sb.append("static ");
      }
      if (method.isFinal()) {
         sb.append("final ");
      }
      sb.append(method.getReturnType().getName() + " ");
      sb.append(method.getName() + "(");
      int paramCount = 0;
      boolean afterFirst = false;
      for (AbstractType paramType : method.getParameterTypes()) {
         if (afterFirst) {
            sb.append(", ");
         }
         else {
            afterFirst = true;
         }
         sb.append(paramType.getName());
         sb.append(" param");
         sb.append(paramCount++);
      }
      sb.append(");");
   }

   protected void appendField(Field stubField, StringBuffer sb, int level) {
      final String INDENT = StringUtil.createLine(" ", level * 3);
      sb.append(INDENT + "/**" + NL);
      sb.append(INDENT + " * @generated" + NL);
      sb.append(INDENT + " */" + NL);
      sb.append(INDENT + stubField.getVisibility().toJavaKeyword() + " ");
      if (stubField.isStatic()) {
         sb.append( "static ");
      }
      if (stubField.isFinal()) {
         sb.append( "final ");
      }
      sb.append(stubField.getType().getName() + " " + stubField.getName());
      if (!StringUtil.isTrimmedEmpty(stubField.getConstantValue())) {
         sb.append("= ");
         sb.append(stubField.getConstantValue());
      }
      sb.append(";");
   }

   protected boolean appendNewMemberSeparator(boolean afterFirstMember, StringBuffer sb) {
      if (afterFirstMember) {
         sb.append(NL + NL);
      }
      return true;
   }
}
