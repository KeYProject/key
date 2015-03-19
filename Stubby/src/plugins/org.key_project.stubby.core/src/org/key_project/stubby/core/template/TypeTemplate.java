package org.key_project.stubby.core.template;

import java.util.List;

import org.key_project.stubby.model.dependencymodel.AbstractType;
import org.key_project.stubby.model.dependencymodel.Field;
import org.key_project.stubby.model.dependencymodel.GenericType;
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
   
   /**
    * Appends the {@link Type}.
    * @param type The {@link Type} to append.
    * @param sb The {@link StringBuffer} to append to.
    * @param level The current indent level.
    */
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
            appendTypeName(extendType, sb);
         }
      }
      if (!type.getImplements().isEmpty()) {
         sb.append(" implements ");
         boolean afterFirst = false;
         for (AbstractType implementsType : type.getImplements()) {
            if (afterFirst) {
               sb.append(", ");
            }
            else {
               afterFirst = true;
            }
            appendTypeName(implementsType, sb);
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

   /**
    * Appends the name of the given {@link AbstractType}.
    * @param type The {@link AbstractType} to append its name.
    * @param sb The {@link StringBuffer} to append to.
    */
   protected void appendTypeName(AbstractType type, StringBuffer sb) {
      sb.append(type.getName());
      if (type instanceof GenericType) {
         GenericType genericType = (GenericType) type;
         if (!genericType.getTypeArguments().isEmpty()) {
            sb.append("<");
            boolean afterFirst = false;
            for (AbstractType arg : genericType.getTypeArguments()) {
               if (afterFirst) {
                  sb.append(", ");
               }
               else {
                  afterFirst = true;
               }
               appendTypeName(arg, sb);
            }
            sb.append(">");
         }
      }
   }

   /**
    * Appends the {@link Method}.
    * @param method The {@link Method} to append.
    * @param sb The {@link StringBuffer} to append to.
    * @param level The current indent level.
    */
   protected void appendMethod(Method method, StringBuffer sb, int level) {
      final String INDENT = StringUtil.createLine(" ", level * 3);
      sb.append(INDENT + "/**" + NL);
      sb.append(INDENT + " * @generated" + NL);
      sb.append(INDENT + " */" + NL);
      sb.append(INDENT + "/*@ normal_behavior" + NL);
      sb.append(INDENT + "  @ requires true;" + NL);
      sb.append(INDENT + "  @ ensures true;" + NL);
      sb.append(INDENT + "  @ assignable \\everything;" + NL);
      sb.append(INDENT + "  @*/" + NL);
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
      if (!method.isConstructor()) {
         sb.append(method.getReturnType().getName() + " ");
      }
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

   /**
    * Appends the {@link Field}.
    * @param field The {@link Field} to append.
    * @param sb The {@link StringBuffer} to append to.
    * @param level The current indent level.
    */
   protected void appendField(Field field, StringBuffer sb, int level) {
      final String INDENT = StringUtil.createLine(" ", level * 3);
      sb.append(INDENT + "/**" + NL);
      sb.append(INDENT + " * @generated" + NL);
      sb.append(INDENT + " */" + NL);
      sb.append(INDENT + field.getVisibility().toJavaKeyword() + " ");
      if (field.isStatic()) {
         sb.append( "static ");
      }
      if (field.isFinal()) {
         sb.append( "final ");
      }
      sb.append(field.getType().getName() + " " + field.getName());
      if (!StringUtil.isTrimmedEmpty(field.getConstantValue())) {
         sb.append("= ");
         sb.append(field.getConstantValue());
      }
      sb.append(";");
   }

   /**
    * Appends the separator between {@link Type} members.
    * @param afterFirstMember Indicates if a previous member is available.
    * @param sb The {@link StringBuffer} to append to.
    * @return The new previous state member available state.
    */
   protected boolean appendNewMemberSeparator(boolean afterFirstMember, StringBuffer sb) {
      if (afterFirstMember) {
         sb.append(NL + NL);
      }
      return true;
   }
}
