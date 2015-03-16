package org.key_project.stubby.core.template;

import java.util.List;

import org.key_project.stubby.model.dependencymodel.AbstractType;
import org.key_project.stubby.model.dependencymodel.Field;
import org.key_project.stubby.model.dependencymodel.Method;
import org.key_project.stubby.model.dependencymodel.Type;
import org.key_project.stubby.model.dependencymodel.Visibility;

public class TypeTemplate {
   protected static String nl;

   public static synchronized TypeTemplate create(String lineSeparator) {
      nl = lineSeparator;
      TypeTemplate result = new TypeTemplate();
      nl = null;
      return result;
   }

   public final String NL = nl == null ? (System.getProperties().getProperty("line.separator")) : nl;

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
   
   public void appendType(Type type, StringBuffer sb, int level) {
      final String INDENT = createSpaces(level * 3);
      sb.append(INDENT + "/**" + NL + INDENT + " * @generated" + NL + INDENT + " */" + NL);
      if (type.getVisibility() != Visibility.DEFAULT) {
         sb.append(INDENT + type.getVisibility().toJavaKeyword() + " ");
         sb.append(type.getKind().toJavaKindKeyword());
      }
      else {
         sb.append(INDENT + type.getKind().toJavaKindKeyword());
      }
      sb.append(" " + type.getSimpleName() + " {");
      List<Field> allFields = type.getFields();
      for (Field stubField : allFields) {
         sb.append(NL + NL + INDENT + "   /**" + NL + INDENT + "    * @generated" + NL + INDENT + "    */");
         sb.append(NL + "   ");
         sb.append(INDENT + stubField.getVisibility().toJavaKeyword() + " ");
         sb.append((stubField.isStatic() ? "static " : ""));
         sb.append((stubField.isFinal() ? "final " : ""));
         sb.append(stubField.getType().getName() + " ");
         sb.append(stubField.getName() + ";" + NL);
      }
      List<Method> allMethods = type.getMethods();
      for (Method method : allMethods) {
         sb.append(NL + NL + INDENT + "   /*@ normal_behavior" + NL + INDENT + "     @ requires true;" + NL + INDENT +"     @ ensures true;" + NL + INDENT + "     @ assignable \\everything;" + NL + INDENT +"     @*/" + NL + INDENT + "   /**" + NL + INDENT + "    * @generated" + NL + INDENT + "    */");
         sb.append(NL + "   ");
         sb.append(INDENT + method.getVisibility().toJavaKeyword() + " ");
         sb.append((method.isAbstract() ? "abstract " : ""));
         sb.append((method.isStatic() ? "static " : ""));
         sb.append((method.isFinal() ? "final " : ""));
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
      for (Type innerType : type.getInnerTypes()) {
         sb.append(NL + NL);
         appendType(innerType, sb, level + 1);
      }
      sb.append(NL + INDENT +"}");
   }

   private String createSpaces(int numOfSpaces) {
      StringBuffer sb = new StringBuffer();
      for (int i=0; i<numOfSpaces; i++) {
         sb.append(" ");
      }
      return sb.toString();
   }
}
