package org.key_project.stubby.core.jdt;

import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.ClassInstanceCreation;
import org.eclipse.jdt.core.dom.FieldAccess;
import org.eclipse.jdt.core.dom.IBinding;
import org.eclipse.jdt.core.dom.IMethodBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.IVariableBinding;
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.MethodInvocation;
import org.eclipse.jdt.core.dom.Modifier;
import org.eclipse.jdt.core.dom.QualifiedName;
import org.eclipse.jdt.core.dom.SimpleName;
import org.eclipse.jdt.core.dom.SuperConstructorInvocation;
import org.eclipse.jdt.core.dom.SuperFieldAccess;
import org.eclipse.jdt.core.dom.SuperMethodInvocation;
import org.eclipse.jdt.core.dom.TypeDeclaration;
import org.key_project.stubby.model.dependencymodel.DependencymodelFactory;
import org.key_project.stubby.model.dependencymodel.Field;
import org.key_project.stubby.model.dependencymodel.ITypeVariableContainer;
import org.key_project.stubby.model.dependencymodel.Method;
import org.key_project.stubby.model.dependencymodel.Type;
import org.key_project.stubby.model.dependencymodel.TypeKind;
import org.key_project.stubby.model.dependencymodel.TypeUsage;
import org.key_project.stubby.model.dependencymodel.TypeVariable;
import org.key_project.stubby.model.dependencymodel.Visibility;

/**
 * An {@link ASTVisitor} used to analyze dependencies.
 * @author Martin Hentschel
 */
public class DependencyAnalyzer extends ASTVisitor {
   /**
    * Utility {@link Map} which maps a full qualified name to its {@link Type}.
    */
   private final Map<String, Type> types = new LinkedHashMap<String, Type>();
   
   /**
    * A {@link List} which contains only created outer {@link Type} and
    * not the representation of inner {@link Type}s.
    */
   private final List<Type> outerTypes = new LinkedList<Type>();

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
    * {@inheritDoc}
    */
   @Override
   public boolean visit(SuperConstructorInvocation node) {
      IMethodBinding methodBinding = node.resolveConstructorBinding();
      if (methodBinding == null) {
         throw new IllegalStateException("Can't resolve super constructor invocation '" + node + "' in the Java build path.");
      }
      ensureMethodExist(methodBinding);
      return true;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean visit(FieldAccess node) {
      IVariableBinding variableBinding = node.resolveFieldBinding();
      if (variableBinding == null) {
         throw new IllegalStateException("Can't resolve field access '" + node + "' in the Java build path.");
      }
      ensureFieldExists(variableBinding);
      return true;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean visit(TypeDeclaration node) {
      ITypeBinding typeBinding = node.resolveBinding();
      if (typeBinding == null) {
         throw new IllegalStateException("Can't resolve type declaration '" + node + "' in the Java build path.");
      }
      ensureTypeExists(typeBinding);
      return super.visit(node);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean visit(MethodDeclaration node) {
      IMethodBinding methodBinding = node.resolveBinding();
      if (methodBinding == null) {
         throw new IllegalStateException("Can't resolve method declaration '" + node + "' in the Java build path.");
      }
      ensureMethodExist(methodBinding);
      return super.visit(node);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean visit(MethodInvocation node) {
      IMethodBinding methodBinding = node.resolveMethodBinding();
      if (methodBinding == null) {
         throw new IllegalStateException("Can't resolve method invocation '" + node + "' in the Java build path.");
      }
      ensureMethodExist(methodBinding);
      return true;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean visit(ClassInstanceCreation node) {
      IMethodBinding methodBinding = node.resolveConstructorBinding();
      if (methodBinding == null) {
         throw new IllegalStateException("Can't resolve class instance creation '" + node + "' in the Java build path.");
      }
      ensureMethodExist(methodBinding);
      return true;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean visit(SuperFieldAccess node) {
      IVariableBinding variableBinding = node.resolveFieldBinding();
      if (variableBinding == null) {
         throw new IllegalStateException("Can't resolve super field access '" + node + "' in the Java build path.");
      }
      ensureFieldExists(variableBinding);
      return true;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean visit(SuperMethodInvocation node) {
      IMethodBinding methodBinding = node.resolveMethodBinding();
      if (methodBinding == null) {
         throw new IllegalStateException("Can't resolve super method invocation '" + node + "' in the Java build path.");
      }
      ensureMethodExist(methodBinding);
      return true;
   }

   /**
    * Returns all created outer {@link Type}s.
    * @return All created outer {@link Type}s.
    */
   public List<Type> getOuterTypes() {
      return outerTypes;
   }
   
   /**
    * Ensures that the given {@link IBinding} is correctly represented in the dependency model.
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
            ensureTypeExists(typeBinding);
         }
      }
   }

   /**
    * Ensures that the given {@link IVariableBinding} is part of dependency model.
    * @param variableBinding The {@link IVariableBinding} to represent.
    */
   public void ensureFieldExists(IVariableBinding variableBinding) {
      variableBinding = variableBinding.getVariableDeclaration();
      ITypeBinding declaringClass = variableBinding.getDeclaringClass();
      if (declaringClass != null) { // In case of local variables the type binding is null
         Type declaringType = ensureTypeExists(declaringClass);
         if (declaringType instanceof Type) { // Nothing needs to be done if Type is not available
            if (!declaringType.containsField(variableBinding.getName())) {
               addField((Type) declaringType, variableBinding);
            }
         }
      }
   }
   
   /**
    * Adds the {@link Field} representation of the given {@link IVariableBinding} to the declaring {@link Type}.
    * @param declaringType The declaring {@link Type} to add {@link Field} to.
    * @param variableBinding The {@link IVariableBinding} to represent as {@link Field}.
    */
   protected void addField(Type declaringType, IVariableBinding variableBinding) {
      Field field = DependencymodelFactory.eINSTANCE.createField();  
      field.setName(variableBinding.getName());
      field.setVisibility(createVisibility(variableBinding.getModifiers()));
      field.setFinal(Modifier.isFinal(variableBinding.getModifiers()));
      field.setStatic(Modifier.isStatic(variableBinding.getModifiers()));
      if (variableBinding.getConstantValue() != null) {
         field.setConstantValue(variableBinding.getConstantValue().toString());
      }
      field.setType(createTypeUsage(variableBinding.getType()));
      declaringType.getFields().add(field);
   }

   /**
    * Ensures that the given {@link IMethodBinding} is part of dependency model.
    * @param methodBinding The {@link IMethodBinding} to represent.
    */
   public void ensureMethodExist(IMethodBinding methodBinding) {
      methodBinding = methodBinding.getMethodDeclaration();
      Type declaringType = ensureTypeExists(methodBinding.getDeclaringClass());
      if (!declaringType.containsMethod(methodBinding.getName(), computeTypeUsages(methodBinding.getParameterTypes()))) {
         addMethod(declaringType, methodBinding);
      }
   }

   /**
    * Computes all type usage names.
    * @param parameterTypes The {@link ITypeBinding}s.
    * @return The type usage names.
    */
   protected String[] computeTypeUsages(ITypeBinding[] parameterTypes) {
      String[] result = new String[parameterTypes.length];
      for (int i = 0; i < result.length; i++) {
         result[i] = computeTypeUsage(parameterTypes[i]);
      }
      return result;
   }

   /**
    * Adds the {@link Method} representation of the given {@link IMethodBinding} to the declaring {@link Type}.
    * @param declaringType The declaring {@link Type} to add {@link Method} to.
    * @param methodBinding The {@link IMethodBinding} to represent as {@link Method}.
    */
   protected void addMethod(Type declaringType, IMethodBinding methodBinding) {
      Method method = DependencymodelFactory.eINSTANCE.createMethod();
      declaringType.getMethods().add(method);
      method.setName(methodBinding.getName());
      method.setVisibility(createVisibility(methodBinding.getModifiers()));
      method.setAbstract(Modifier.isAbstract(methodBinding.getModifiers()));
      method.setFinal(Modifier.isFinal(methodBinding.getModifiers()));
      method.setStatic(Modifier.isStatic(methodBinding.getModifiers()));
      method.setConstructor(methodBinding.isConstructor());
      for (ITypeBinding typeParameter : methodBinding.getTypeParameters()) {
         addTypeVariable(method, typeParameter);
      }
      for (ITypeBinding parameterType : methodBinding.getParameterTypes()) {
         method.getParameterTypes().add(createTypeUsage(parameterType));
      }
      for (ITypeBinding thrownException : methodBinding.getExceptionTypes()) {
         method.getThrows().add(createTypeUsage(thrownException));
      }
      method.setReturnType(createTypeUsage(methodBinding.getReturnType()));
   }

   /**
    * Ensures that the given {@link ITypeBinding} is part of dependency model.
    * @param typeBinding The {@link ITypeBinding} to represent.
    */
   public Type ensureTypeExists(ITypeBinding typeBinding) {
      typeBinding = toTypeDeclaration(typeBinding);
      String typeName = typeBinding.getQualifiedName();
      Type type = (Type)types.get(typeName);
      if (type == null) {
         type = DependencymodelFactory.eINSTANCE.createType();
         type.setName(typeName);
         type.setSimpleName(typeBinding.getName());
         type.setVisibility(createVisibility(typeBinding.getModifiers()));
         type.setKind(createTypeKind(typeBinding));
         type.setFinal(Modifier.isFinal(typeBinding.getModifiers()));
         type.setStatic(Modifier.isStatic(typeBinding.getModifiers()));
         type.setAbstract(Modifier.isAbstract(typeBinding.getModifiers()));
         type.setSource(typeBinding.isFromSource());
         types.put(typeName, type);
         ITypeBinding[] typeParameters = typeBinding.getTypeParameters();
         for (ITypeBinding typeParameter : typeParameters) {
            addTypeVariable(type, typeParameter);
         }
         ITypeBinding superClass = typeBinding.getSuperclass();
         if (superClass != null) {
            type.getExtends().add(createTypeUsage(superClass));                     
         }
         ITypeBinding[] interfaceArray = typeBinding.getInterfaces();
         for (ITypeBinding interfaceType : interfaceArray) {
            if (interfaceType.getSuperclass() == typeBinding.getSuperclass()) {
               type.getExtends().add(createTypeUsage(interfaceType));
            } 
            else {
               type.getImplements().add(createTypeUsage(interfaceType));
            }
         }
         ITypeBinding declaringClass = typeBinding.getDeclaringClass();
         if (declaringClass != null) {
            Type parentType = (Type)ensureTypeExists(declaringClass);
            parentType.getInnerTypes().add(type);                                                                                                       
         }
         else {
            outerTypes.add(type);
         }
         if (typeBinding.getPackage() != null) {
            type.setPackage(typeBinding.getPackage().getName());
         }
      }
      return type;
   }
   
   /**
    * Computes the type declaration of the given {@link ITypeBinding}.
    * @param typeBinding The {@link ITypeBinding}.
    * @return The type declaration of the given {@link ITypeBinding}.
    */
   protected ITypeBinding toTypeDeclaration(ITypeBinding typeBinding) {
      while (typeBinding.isArray()) {
         typeBinding = typeBinding.getComponentType();
      }
      return typeBinding.getTypeDeclaration();
   }

   /**
    * Adds the {@link TypeVariable} representation of the given {@link ITypeBinding} to the container {@link ITypeVariableContainer}.
    * @param containerType The container {@link ITypeVariableContainer} to add {@link TypeVariable} to.
    * @param typeParameter The {@link ITypeBinding} to represent as {@link TypeVariable}.
    */
   protected void addTypeVariable(ITypeVariableContainer containerType, ITypeBinding typeParameter) {
      TypeVariable typeVar = DependencymodelFactory.eINSTANCE.createTypeVariable();
      typeVar.setName(typeParameter.getQualifiedName());
      containerType.getTypeVariables().add(typeVar);
      ITypeBinding[] boundBindings = typeParameter.getTypeBounds();
      if (boundBindings.length == 0) {
         ITypeBinding superBinding = typeParameter.getSuperclass();
         typeVar.setType(createTypeUsage(superBinding));
      }
      else if (boundBindings.length == 1) {
         typeVar.setType(createTypeUsage(boundBindings[0]));
      }
      else {
         throw new IllegalStateException("Type variables with not exactly one bound are not supported.");
      }
   }
   
   /**
    * Creates a {@link TypeUsage} representing the given {@link ITypeBinding}.
    * @param typeBinding The {@link ITypeBinding} to represent.
    * @return The created {@link TypeUsage}.
    */
   protected TypeUsage createTypeUsage(ITypeBinding typeBinding) {
      // Ensure that the type exists.
      ensureUsedTypesExist(typeBinding);
      // Create type usage.
      TypeUsage tu = DependencymodelFactory.eINSTANCE.createTypeUsage();
      tu.setType(computeTypeUsage(typeBinding));
      ITypeBinding erasure = typeBinding.getErasure();
      if (erasure != null) {
         tu.setGenericFreeType(typeBinding.getErasure().getQualifiedName());
      }
      else {
         tu.setGenericFreeType(tu.getType());
      }
      return tu;
   }
   
   /**
    * Ensures that all involved {@link ITypeBinding} are part of the dependency model.
    * @param typeBinding The starting {@link ITypeBinding}.
    */
   protected void ensureUsedTypesExist(ITypeBinding typeBinding) {
      // Treat arrays
      while (typeBinding.isArray()) {
         typeBinding = typeBinding.getComponentType();
      }
      // Treat generic types (only of array components)
      if (typeBinding.isParameterizedType()) {
         ITypeBinding[] arguments = typeBinding.getTypeArguments();
         for (ITypeBinding argument : arguments) {
            ensureUsedTypesExist(argument);
         }
         ensureTypeExists(typeBinding);
      }
      else if (typeBinding.isWildcardType()) {
         ensureTypeExists(typeBinding.getErasure());
      }
      else if (typeBinding.isTypeVariable()) {
         ensureTypeExists(typeBinding.getErasure());
      }
      else if (!typeBinding.isPrimitive()) {
         ensureTypeExists(typeBinding);
      }
   }

   /**
    * Computes the type usage name.
    * @param typeBinding The {@link ITypeBinding} to compute its type usage name.
    * @return The computed type usage name.
    */
   protected String computeTypeUsage(ITypeBinding typeBinding) {
      return typeBinding.getQualifiedName();
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
    * Creates the {@link TypeKind} of the given {@link ITypeBinding}.
    * @param typeBinding The {@link ITypeBinding}.
    * @return The {@link TypeKind} of the given {@link ITypeBinding}.
    */
   protected TypeKind createTypeKind(ITypeBinding typeBinding) {
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
}
