package org.key_project.stubby.core.jdt;

import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.eclipse.emf.ecore.EObject;
import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.ClassInstanceCreation;
import org.eclipse.jdt.core.dom.FieldAccess;
import org.eclipse.jdt.core.dom.IBinding;
import org.eclipse.jdt.core.dom.IMethodBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.IVariableBinding;
import org.eclipse.jdt.core.dom.MethodInvocation;
import org.eclipse.jdt.core.dom.Modifier;
import org.eclipse.jdt.core.dom.QualifiedName;
import org.eclipse.jdt.core.dom.SimpleName;
import org.eclipse.jdt.core.dom.SuperConstructorInvocation;
import org.eclipse.jdt.core.dom.SuperFieldAccess;
import org.eclipse.jdt.core.dom.SuperMethodInvocation;
import org.key_project.stubby.model.dependencymodel.AbstractType;
import org.key_project.stubby.model.dependencymodel.ArrayType;
import org.key_project.stubby.model.dependencymodel.Datatype;
import org.key_project.stubby.model.dependencymodel.DependencymodelFactory;
import org.key_project.stubby.model.dependencymodel.Field;
import org.key_project.stubby.model.dependencymodel.GenericType;
import org.key_project.stubby.model.dependencymodel.ITypeVariableContainer;
import org.key_project.stubby.model.dependencymodel.Method;
import org.key_project.stubby.model.dependencymodel.Type;
import org.key_project.stubby.model.dependencymodel.TypeKind;
import org.key_project.stubby.model.dependencymodel.TypeVariable;
import org.key_project.stubby.model.dependencymodel.Visibility;
import org.key_project.stubby.model.dependencymodel.WildcardType;

/**
 * An {@link ASTVisitor} used to analyze dependencies.
 * @author Martin Hentschel
 */
public class DependencyAnalyzer extends ASTVisitor {
   /**
    * Utility {@link Map} which maps a full qualified name to its {@link AbstractType}.
    */
   private final Map<String, AbstractType> types = new LinkedHashMap<String, AbstractType>();
   
   /**
    * A {@link List} which contains only created outer {@link AbstractType} and
    * not the representation of inner {@link AbstractType}s.
    */
   private final List<AbstractType> outerTypes = new LinkedList<AbstractType>();

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean visit(QualifiedName node) {
      ensureMembersExist(node.resolveBinding());
      return true;
   }
  
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean visit(SimpleName node) {
      ensureMembersExist(node.resolveBinding());
      return true;
   }
   
   /**
    * Ensures that the representation of the given {@link IBinding} exist.
    * @param binding The {@link IBinding} to represent.
    */
   protected void ensureMembersExist(IBinding binding) {
      if (binding instanceof IVariableBinding) {
         ensureFieldExists((IVariableBinding) binding);
      }
      else if (binding instanceof IMethodBinding) {
         ensureMethodExist((IMethodBinding) binding);
      }
      else if (binding instanceof ITypeBinding) {
         ITypeBinding typeBinding = (ITypeBinding) binding;
         if (!typeBinding.isTypeVariable()) {
            ensureTypeExists((Type)null, typeBinding);
         }
      }
   }

   /**
    * Ensures that the {@link AbstractType} representation of the given {@link ITypeBinding} exist.
    * @param typeBinding The {@link ITypeBinding} to represent as {@link Type}.
    * @return The created {@link AbstractType} if it does not exist before or the already existing instance.
    */
   protected AbstractType ensureTypeExists(ITypeVariableContainer containerType, ITypeBinding typeBinding) {
      if (typeBinding.isTypeVariable()) {
         AbstractType result = searchTypeVariable(containerType.getTypeVariables(), typeBinding);
         if (result == null) {
            EObject parent = containerType.eContainer();
            if (parent instanceof Type) {
               result = ensureTypeExists((Type) parent, typeBinding);
            }
         }
         return result;
      }
      else {
         if (typeBinding.isWildcardType()) {
            WildcardType wildcardType = createWildcardType(typeBinding);
            return wildcardType;
         }
         else if (typeBinding.isPrimitive()) {
            Datatype datatyp = createDataTyp(typeBinding);
            return datatyp;
         }
         else if (typeBinding.isArray()) {
            ArrayType arrayTyp = createArrayType(containerType, typeBinding);
            return arrayTyp;
         }
         else if (typeBinding.isParameterizedType()) {
            GenericType genericType = createGenericType(containerType, typeBinding);
            return genericType;
         }
         else {
            Type type = createType(containerType, typeBinding);
            return type;
         }
      }
   }
   
   /**
    * Searches the {@link TypeVariable} representing the given {@link ITypeBinding}.
    * @param list The available {@link TypeVariable}s.
    * @param typeBinding The {@link ITypeBinding} to search its representation.
    * @return The found {@link TypeVariable} or {@code null} if non was found.
    */
   protected TypeVariable searchTypeVariable(List<TypeVariable> list, ITypeBinding typeBinding) {
      TypeVariable result = null;
      Iterator<TypeVariable> iter = list.iterator();
      while (result == null && iter.hasNext()) {
         TypeVariable next = iter.next();
         if (next.getName().equals(typeBinding.getName())) {
            result = next;
         }
      }
      return result;
   }
   
   /**
    * Creates the {@link WildcardType} representing the given {@link ITypeBinding}.
    * @param typeBinding The {@link ITypeBinding}.
    * @return The created {@link WildcardType} representing the given {@link ITypeBinding}.
    */
   protected WildcardType createWildcardType(ITypeBinding typeBinding) {
      WildcardType wildcardtyp = (WildcardType)types.get("?");
      if (wildcardtyp == null) {
         wildcardtyp = DependencymodelFactory.eINSTANCE.createWildcardType();
         wildcardtyp.setName("?");
         wildcardtyp.setSource(typeBinding.isFromSource());
         types.put("?", wildcardtyp);
         outerTypes.add(wildcardtyp);
      }
      return wildcardtyp;
   }

   /**
    * Creates the {@link Datatype} representing the given {@link ITypeBinding}.
    * @param typeBinding The {@link ITypeBinding}.
    * @return The created {@link Datatype} representing the given {@link ITypeBinding}.
    */
   protected Datatype createDataTyp(ITypeBinding typeBinding) {
      String typeName = typeBinding.getQualifiedName();
      Datatype datatyp = (Datatype)types.get(typeName);
      if (datatyp == null) {
         datatyp = DependencymodelFactory.eINSTANCE.createDatatype();
         datatyp.setName(typeBinding.getName());
         datatyp.setSource(typeBinding.isFromSource());
         types.put(typeName, datatyp);
         outerTypes.add(datatyp);
      }
      return datatyp;
   }
   
   /**
    * Creates the {@link ArrayType} representing the given {@link ITypeBinding}.
    * @param containerType The parent {@link ITypeVariableContainer}.
    * @param typeBinding The {@link ITypeBinding}.
    * @return The created {@link ArrayType} representing the given {@link ITypeBinding}.
    */
   protected ArrayType createArrayType(ITypeVariableContainer containerType, ITypeBinding typeBinding) {
      String typeName = typeBinding.getQualifiedName();
      ArrayType arrayTyp = (ArrayType)types.get(typeName);
      if(arrayTyp == null) {
         arrayTyp = DependencymodelFactory.eINSTANCE.createArrayType();
         arrayTyp.setName(typeBinding.getQualifiedName());
         arrayTyp.setSource(typeBinding.isFromSource());
         ITypeBinding baseType = typeBinding.getComponentType();
         if (baseType != null) {
            arrayTyp.setBaseType(ensureTypeExists(containerType, baseType));
         }
         types.put(typeName, arrayTyp);
         outerTypes.add(arrayTyp);
      }
      return arrayTyp;
   }
   
   /**
    * Creates the {@link GenericType} representing the given {@link ITypeBinding}.
    * @param containerType The parent {@link ITypeVariableContainer}.
    * @param typeBinding The {@link ITypeBinding}.
    * @return The created {@link GenericType} representing the given {@link ITypeBinding}.
    */
   protected GenericType createGenericType(ITypeVariableContainer containerType, ITypeBinding typeBinding) {
      String typeName = typeBinding.getQualifiedName();
      GenericType genericType = (GenericType)types.get(typeName);
      if (genericType == null) {
         genericType = DependencymodelFactory.eINSTANCE.createGenericType();
         genericType.setName(typeBinding.getJavaElement().getElementName());
         genericType.setSource(typeBinding.isFromSource());
         ITypeBinding baseType = typeBinding.getTypeDeclaration();
         if(baseType != null){
         genericType.setBaseType(ensureTypeExists(containerType, baseType));
         }
         ITypeBinding[] arguments = typeBinding.getTypeArguments();
         for (ITypeBinding argument : arguments) {
            AbstractType argumentType = ensureTypeExists(containerType, argument);
            genericType.getTypeArguments().add(argumentType);
         }
         types.put(typeName, genericType);
         outerTypes.add(genericType);
      }
      return genericType;
   }

   /**
    * Creates the {@link Type} representing the given {@link ITypeBinding}.
    * @param containerType The parent {@link ITypeVariableContainer}.
    * @param typeBinding The {@link ITypeBinding}.
    * @return The created {@link Type} representing the given {@link ITypeBinding}.
    */
   protected Type createType(ITypeVariableContainer containerType, ITypeBinding typeBinding) {
      String typeName = typeBinding.getQualifiedName();
      Type type = (Type)types.get(typeName);
      if (type == null) {
         type = DependencymodelFactory.eINSTANCE.createType();
         type.setName(typeName);
         type.setSimpleName(typeBinding.getName());
         if (typeBinding.getPackage() != null) {
            type.setPackage(typeBinding.getPackage().getName());
         }
         type.setVisibility(createVisibility(typeBinding.getModifiers()));
         type.setKind(createKind(typeBinding));
         type.setFinal(Modifier.isFinal(typeBinding.getModifiers()));
         type.setStatic(Modifier.isStatic(typeBinding.getModifiers()));
         type.setAbstract(Modifier.isAbstract(typeBinding.getModifiers()));
         type.setSource(typeBinding.isFromSource());
         types.put(typeName, type);
         ITypeBinding[] typeParameters = typeBinding.getTypeParameters();
         for (ITypeBinding typeParameter : typeParameters) {
            if(typeParameter != null){
               type.getTypeVariables().add(createTypeVariable(containerType, typeParameter));
            }
         }
         ITypeBinding superClass = typeBinding.getSuperclass();
         if (superClass != null) {
            type.getExtends().add(ensureTypeExists(type, superClass));                     
         }
         ITypeBinding[] interfaceArray = typeBinding.getInterfaces();
         for (ITypeBinding interfaceType : interfaceArray) {
            if(interfaceType.getSuperclass() == typeBinding.getSuperclass()) {
               type.getExtends().add(ensureTypeExists(type, interfaceType));
            } else {
               type.getImplements().add(ensureTypeExists(type, interfaceType));
            }
         }
         ITypeBinding declaringClass = typeBinding.getDeclaringClass();
         if (declaringClass != null) {
            Type parentType = (Type)ensureTypeExists(type, declaringClass);
            parentType.getInnerTypes().add(type);                                                                                                       
         }
         else {
            outerTypes.add(type);
         }
      }
      return type;
   }
   
   /**
    * Creates the {@link TypeKind} of the given {@link ITypeBinding}.
    * @param typeBinding The {@link ITypeBinding}.
    * @return The {@link TypeKind} of the given {@link ITypeBinding}.
    */
   protected TypeKind createKind(ITypeBinding typeBinding) {
      if (typeBinding.isClass()) {
         return TypeKind.CLASS;
      }
      else if (typeBinding.isInterface()) {
         return TypeKind.INTERFACE;
      }
      else if (typeBinding.isAnnotation()) {
         return TypeKind.ANNOTATION;
      }
      else if (typeBinding.isEnum()) {
         return TypeKind.ENUM;
      }
      else {
         return null;
      }
   }
   
   /**
    * Creates the {@link Visibility} of the given modifiers.
    * @param modifiers The modifiers.
    * @return The {@link Visibility} of the given modifiers.
    */
   protected Visibility createVisibility(int modifiers) {
      if (Modifier.isPublic(modifiers)) {
         return Visibility.PUBLIC;
      }
      else if (Modifier.isProtected(modifiers)) {
         return Visibility.PROTECTED;
      }
      else if (Modifier.isPrivate(modifiers)) {
         return Visibility.PRIVATE;
      }
      else {
         return Visibility.DEFAULT;
      }
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean visit(SuperConstructorInvocation node) {
      IMethodBinding methodBinding = node.resolveConstructorBinding();
      ensureMethodExist(methodBinding);
      return true;
   }

   /**
    * Ensures that the {@link Method} representation of the given {@link IMethodBinding} exist.
    * @param methodBinding The {@link IMethodBinding} to represent as {@link Method}.
    */
   protected void ensureMethodExist(IMethodBinding methodBinding) {
      methodBinding = methodBinding.getMethodDeclaration();
      AbstractType methodType = ensureTypeExists((Type)null, methodBinding.getDeclaringClass());
      methodType = findBaseType(methodType);
      if (methodType instanceof Type) { // Nothing needs to be done if Typ is not available
         Type typ = (Type)methodType;
         if (!containsMethod(typ, methodBinding.getName(), methodBinding.getParameterTypes())) {
            createMethodFromDeclaration(typ, methodBinding);
         }              
      }
   }

   /**
    * Proves if declaration {@link String} of a {@link Method} is already filed in typ {@link Type} 
    * @param typ {@link Type} 
    * @param declaration {@link String} of a {@link Method}
    * @return true {@link Boolean} if declaration {@link String} already exists and false {@link Boolean} if not
    */
   protected static boolean containsMethod(Type typ, String declaration, ITypeBinding[] typeparams) {
      for (Method currentMethod : typ.getMethods()) {
         if (currentMethod.getName().equals(declaration)) { 
            List<AbstractType> paramTyps = currentMethod.getParameterTypes();
            if (paramTyps.size() == typeparams.length) {
               int i = 0;
               boolean allParamEquals = true;
               for (AbstractType paramTyp : paramTyps) {
                  if (!paramTyp.getName().equals(typeparams[i].getQualifiedName())) {
                     allParamEquals = false;
                  }
                  i++;
               }
               if (allParamEquals) {
                  return true;
               }
            }
         }
      }
      return false;
   }
   
   /**
    * Method creates {@link Method} from given {@link String} for given {@link Type}
    * @param typ {@link Type}
    * @param superMethodDeclaration {@link String}
    */
   protected void createMethodFromDeclaration(Type typ, IMethodBinding methodBinding) {
      Method method = DependencymodelFactory.eINSTANCE.createMethod();
      typ.getMethods().add(method);
      methodBinding = methodBinding.getMethodDeclaration();
      method.setName(methodBinding.getName());
      method.setVisibility(createVisibility(methodBinding.getModifiers()));
      method.setAbstract(Modifier.isAbstract(methodBinding.getModifiers()));
      method.setFinal(Modifier.isFinal(methodBinding.getModifiers()));
      method.setStatic(Modifier.isStatic(methodBinding.getModifiers()));
      method.setConstructor(methodBinding.isConstructor());
      for (ITypeBinding typeParameter : methodBinding.getTypeParameters()) {
         method.getTypeVariables().add(createTypeVariable(typ, typeParameter));
      }
      for (ITypeBinding paramType : methodBinding.getParameterTypes()) {
         AbstractType emfParamType = ensureTypeExists(method, paramType);
         assert emfParamType != null;
         method.getParameterTypes().add(emfParamType);
      }
      for (ITypeBinding methodThrows : methodBinding.getExceptionTypes()) {
         AbstractType methodThrow = ensureTypeExists(method, methodThrows);
         method.getThrows().add(methodThrow);
      }
      method.setReturnType(ensureTypeExists(method, methodBinding.getReturnType()));
   }
   
   /**
    * Creates the {@link TypeVariable} representing the given {@link ITypeBinding}.
    * @param containerType The parent {@link ITypeVariableContainer}.
    * @param typeParameter The {@link ITypeBinding}.
    * @return The created {@link TypeVariable} representing the given {@link ITypeBinding}.
    */
   protected TypeVariable createTypeVariable(ITypeVariableContainer containerType, ITypeBinding typeParameter) {
      TypeVariable typeVar = DependencymodelFactory.eINSTANCE.createTypeVariable();
      typeVar.setName(typeParameter.getQualifiedName());
      ITypeBinding[] boundBindings = typeParameter.getTypeBounds();
      if (boundBindings.length == 0) {
         ITypeBinding superBinding = typeParameter.getSuperclass();
         typeVar.setType(ensureTypeExists(containerType, superBinding));
      }
      else if (boundBindings.length == 1) {
         typeVar.setType(ensureTypeExists(containerType, boundBindings[0]));
      }
      else {
         throw new IllegalStateException("Type variable with not exactly one bound is not supported.");
      }
      return typeVar;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean visit(FieldAccess node) {
      IVariableBinding variableBinding = node.resolveFieldBinding();
      ensureFieldExists(variableBinding);
      return true;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean visit(MethodInvocation node) {
      IMethodBinding methodBinding = node.resolveMethodBinding();
      ensureMethodExist(methodBinding);
      return true;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean visit(ClassInstanceCreation node) {
      IMethodBinding methodBinding = node.resolveConstructorBinding();
      ensureMethodExist(methodBinding);
      return true;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean visit(SuperFieldAccess node) {
      IVariableBinding variableBinding = node.resolveFieldBinding();
      ensureFieldExists(variableBinding);
      return true;
   }
   
   /**
    * Ensures that the {@link Field} representation of the given {@link IVariableBinding} exist.
    * @param variableBinding The {@link IVariableBinding} to represent as {@link Field}.
    */
   protected void ensureFieldExists(IVariableBinding variableBinding) {
      ITypeBinding typeBinding = variableBinding.getDeclaringClass();
      if (typeBinding != null) { // In case of local variables the type binding is null
         AbstractType type = ensureTypeExists((Type)null, variableBinding.getDeclaringClass());
         type = findBaseType(type);
         if (type instanceof Type) { // Nothing needs to be done if Type is not available
            if (!containsField((Type) type, variableBinding.getName())) {
               createFieldFromDeclaration((Type) type, variableBinding);
            }
         }
      }
   }
   
   /**
    * Proves if declaration {@link String} of a {@link Field} is already filed in typ {@link Type} 
    * @param typ {@link Type}
    * @param declaration {@link String} of a {@link Field}
    * @return true {@link Boolean} if declaration {@link String} already exists and false {@link Boolean} if not
    */
   protected static boolean containsField(Type typ, String declaration) {
      for (Field currentField : typ.getFields()) {
         if(currentField.getName().equals(declaration)) {
            return true;
         }
      }
      return false;
   }
   
   /**
    * Method creates {@link Field} from given {@link String} for given {@link Type} 
    * @param typ {@link Type}
    * @param superFieldDeclaration {@link String}
    */
   protected void createFieldFromDeclaration(Type typ, IVariableBinding variableBinding) {
      Field field = DependencymodelFactory.eINSTANCE.createField();  
      field.setName(variableBinding.getName());
      field.setVisibility(createVisibility(variableBinding.getModifiers()));
      field.setFinal(Modifier.isFinal(variableBinding.getModifiers()));
      field.setStatic(Modifier.isStatic(variableBinding.getModifiers()));
      if (variableBinding.getConstantValue() != null) {
         field.setConstantValue(variableBinding.getConstantValue().toString());
      }
      AbstractType varType = ensureTypeExists(typ, variableBinding.getType());
      if (varType != null) {
         field.setType(varType);
      }
      typ.getFields().add(field);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean visit(SuperMethodInvocation node) {
      IMethodBinding methodBinding = node.resolveMethodBinding();
      ensureMethodExist(methodBinding);
      return true;
   }

   /**
    * Finds the base type of the given {@link AbstractType}.
    * @param baseType The current {@link AbstractType}.
    * @return The base {@link AbstractType}.
    */
   protected static AbstractType findBaseType(AbstractType baseType) {
      while (baseType instanceof GenericType) {
         baseType = ((GenericType) baseType).getBaseType();
      }
      return baseType;
   }

   /**
    * Returns all created outer {@link AbstractType}s.
    * @return All created outer {@link AbstractType}s.
    */
   public List<AbstractType> getOuterTypes() {
      return outerTypes;
   }
}
