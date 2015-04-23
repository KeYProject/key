package org.key_project.stubby.core.template;

import java.util.List;

import org.key_project.stubby.model.dependencymodel.Field;
import org.key_project.stubby.model.dependencymodel.ITypeVariableContainer;
import org.key_project.stubby.model.dependencymodel.Method;
import org.key_project.stubby.model.dependencymodel.Type;
import org.key_project.stubby.model.dependencymodel.TypeUsage;
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
    * If {@code true} generated stubs are generic free, otherwise generics might be contained.
    */
   private final boolean genericFree;

   /**
    * Creates a new {@link TypeTemplate}.
    * @param lineSeparator The line separator to use.
    * @return The created {@link TypeTemplate}.
    */
   public static synchronized TypeTemplate create(String lineSeparator) {
      nl = lineSeparator;
      TypeTemplate result = new TypeTemplate(false);
      nl = null;
      return result;
   }
   
   /**
    * Constructor.
    * @param genericFree If {@code true} generated stubs are generic free, otherwise generics might be contained.
    */
   public TypeTemplate(boolean genericFree) {
      this.genericFree = genericFree;
   }

   /**
    * The new line separator to use.
    */
   public final String NL = nl == null ? (StringUtil.NEW_LINE) : nl;

   /**
    * Generates the Java file content.
    * @param type The {@link Type} to generate stub file for.
    * @return The created Java file.
    */
   public String generate(Type type) {
      final StringBuffer sb = new StringBuffer();
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
      appendTypeVariables(type, sb);
      if (!type.getExtends().isEmpty()) {
         sb.append(" extends ");
         boolean afterFirst = false;
         for (TypeUsage extendType : type.getExtends()) {
            if (afterFirst) {
               sb.append(", ");
            }
            else {
               afterFirst = true;
            }
            appendTypeUsage(extendType, sb);
         }
      }
      if (!type.getImplements().isEmpty()) {
         sb.append(" implements ");
         boolean afterFirst = false;
         for (TypeUsage implementsType : type.getImplements()) {
            if (afterFirst) {
               sb.append(", ");
            }
            else {
               afterFirst = true;
            }
            appendTypeUsage(implementsType, sb);
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
    * Appends the {@link TypeVariable}s.
    * @param container The {@link ITypeVariableContainer} which provides the {@link TypeVariable}s to append.
    * @param sb The {@link StringBuffer} to write to.
    */
   protected void appendTypeVariables(ITypeVariableContainer container, StringBuffer sb) {
      if (!genericFree && !container.getTypeVariables().isEmpty()) {
         sb.append("<");
         boolean afterFirst = false;
         for (TypeVariable var : container.getTypeVariables()) {
            if (afterFirst) {
               sb.append(", ");
            }
            else {
               afterFirst = true;
            }
            sb.append(var.getName());
            sb.append(" extends ");
            appendTypeUsage(var.getType(), sb);
         }
         sb.append(">");
      }
   }

   /**
    * Appends the {@link TypeUsage} to the given {@link StringBuffer}.
    * @param typeUsage The {@link TypeUsage} to append.
    * @param sb The {@link StringBuffer} to write to.
    */
   protected void appendTypeUsage(TypeUsage typeUsage, StringBuffer sb) {
      if (genericFree) {
         sb.append(typeUsage.getGenericFreeType());
      }
      else {
         sb.append(typeUsage.getType());
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
      sb.append(INDENT + "/*@ ");
      if (!Visibility.DEFAULT.equals(method.getVisibility())) {
         sb.append(method.getVisibility().toJavaKeyword() + " ");         
      }
      sb.append("behavior" + NL);
      sb.append(INDENT + "  @ requires true;" + NL);
      sb.append(INDENT + "  @ ensures true;" + NL);
      sb.append(INDENT + "  @ assignable \\everything;" + NL);
      sb.append(INDENT + "  @*/" + NL);
      sb.append(INDENT);
      if (!Visibility.DEFAULT.equals(method.getVisibility())) {
         sb.append(method.getVisibility().toJavaKeyword() + " ");         
      }
      if (method.isStatic()) {
         sb.append("static ");
      }
      if (method.isAbstract()) {
         sb.append("abstract ");
      }
      if (method.isFinal()) {
         sb.append("final ");
      }
      appendTypeVariables(method, sb);
      if (!method.isConstructor()) {
         appendTypeUsage(method.getReturnType(), sb);
         sb.append(" ");
      }
      sb.append(method.getName() + "(");
      int paramCount = 0;
      boolean afterFirst = false;
      for (TypeUsage paramType : method.getParameterTypes()) {
         if (afterFirst) {
            sb.append(", ");
         }
         else {
            afterFirst = true;
         }
         appendTypeUsage(paramType, sb);
         sb.append(" param");
         sb.append(paramCount++);
      }
      sb.append(")");
      if (!method.getThrows().isEmpty()) {
         sb.append(" throws ");
         afterFirst = false;
         for (TypeUsage thrownType : method.getThrows()) {
            if (afterFirst) {
               sb.append(", ");
            }
            else {
               afterFirst = true;
            }
            appendTypeUsage(thrownType, sb);
         }
      }
      sb.append(";");
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
      sb.append(INDENT);
      if (!Visibility.DEFAULT.equals(field.getVisibility())) {
         sb.append(field.getVisibility().toJavaKeyword() + " ");
      }
      if (field.isStatic()) {
         sb.append( "static ");
      }
      if (field.isFinal()) {
         sb.append( "final ");
      }
      appendTypeUsage(field.getType(), sb);
      sb.append(" ");
      sb.append(field.getName());
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
