package org.key_project.stubby.core.generator;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.net.URL;
import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.Status;
import org.eclipse.emf.codegen.merge.java.JControlModel;
import org.eclipse.emf.codegen.merge.java.JMerger;
import org.eclipse.emf.codegen.merge.java.facade.FacadeHelper;
import org.eclipse.emf.codegen.merge.java.facade.jdom.JDOMFacadeHelper;
import org.eclipse.emf.codegen.util.CodeGenUtil;
import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.emf.ecore.resource.ResourceSet;
import org.eclipse.emf.ecore.resource.impl.ResourceSetImpl;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IPackageFragmentRoot;
import org.eclipse.jdt.core.dom.ASTNode;
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
import org.key_project.stubby.core.Activator;
import org.key_project.stubby.core.template.TypeTemplate;
import org.key_project.stubby.model.dependencymodel.AbstractType;
import org.key_project.stubby.model.dependencymodel.ArrayType;
import org.key_project.stubby.model.dependencymodel.Datatype;
import org.key_project.stubby.model.dependencymodel.DependencyModel;
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
import org.key_project.util.jdt.JDTUtil;
import org.osgi.framework.Bundle;
//import org.eclipse.jdt.core.dom.ArrayType;

/**
 * This class is the main entry point to use the stub generation.
 * 
 * @author Martin Hentschel
 */
public final class StubGeneratorUtil {
   /**
    * Indicates if the dependency model should be saved during stub generation.
    */
   public static final boolean SAVE_DEPENDENCY_MODEL = true;
   
   /**
    * The file extension used to store dependency models.
    */
   public static final String DEPENDENCY_MODEL_FILE_EXTENSION = "dependencymodel";
   
   /**
    * The name of the folder in an {@link IProject} which will contain the generated stubs.
    */
   public static final String STUB_FOLDER_NAME = "stubs";

   /**
    * Forbid instances by this private constructor.
    */
   private StubGeneratorUtil() {
   }
   
   /**
    * Generates stubs for the given {@link IJavaProject}.
    * @param project The {@link IJavaProject} to generate stubs for.
    */
   public static void generateStubs(IJavaProject project) throws CoreException {
      try {
         // Find compilation units in source folders
         List<IPackageFragmentRoot> sourceFolders = JDTUtil.getSourceFolders(project);
         List<ICompilationUnit> compilationUnits = JDTUtil.listCompilationUnit(sourceFolders);
         // Create dependency model
         DependencyModel dependencyModel = DependencymodelFactory.eINSTANCE.createDependencyModel();
         for (ICompilationUnit unit : compilationUnits) {
            ASTNode ast = JDTUtil.parse(unit);
            List<AbstractType> types = extractTypesAndMembers(ast);
            dependencyModel.getTypes().addAll(types);
         }
         // Save dependency model in project
         if (SAVE_DEPENDENCY_MODEL) {
            IFile emfFile = project.getProject().getFile("Dependencymodel." + DEPENDENCY_MODEL_FILE_EXTENSION);
            ResourceSet rst = new ResourceSetImpl();
            Resource resource = rst.createResource(URI.createPlatformResourceURI(emfFile.getFullPath().toString(), true));
            resource.getContents().add(dependencyModel);
            resource.save(Collections.EMPTY_MAP);
         }
         // Generate stubs with help of JET
         buildStubStructure(dependencyModel, project);
      }
      catch (IOException e) {
         throw new CoreException(new Status(IStatus.ERROR, "BUNDLE_ID", e.getMessage(), e));
      }
   }
   
   protected static void buildStubStructure(DependencyModel dependencyModel, IJavaProject project) throws CoreException, IOException {
      for (AbstractType abstractType : dependencyModel.getTypes()) {
         if (abstractType instanceof Type && !abstractType.isSource()) {
            // Create new content
            TypeTemplate template = new TypeTemplate();
            String content = template.generate(abstractType);
            // Save file
            Type type = (Type) abstractType;
            String projectStubFolder = STUB_FOLDER_NAME;
            String[] res = type.getPackage().split("\\.");
            String projectSimpleName = type.getSimpleName() + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT;  
            IProject stubProject = project.getProject();
            IFolder stubFolder = stubProject.getFolder(projectStubFolder);
            if (!stubFolder.exists()) { 
               stubFolder.create(true, true, null);
            }
            for (String stubSub : res) {
               stubFolder = stubFolder.getFolder(stubSub);
               if (!stubFolder.exists()) {
                  stubFolder.create(true, true, null);
               }
            }
            IFile stubJavaClass = stubFolder.getFile(projectSimpleName);
            if (!stubJavaClass.exists()) {
               // Create file
               stubJavaClass.create(new ByteArrayInputStream(content.getBytes()), true, null);
            }
            else {
               // Merge new with existing content
               JControlModel controlModel = new JControlModel();
               controlModel.setConvertToStandardBraceStyle(true);
               FacadeHelper facadeHelper = CodeGenUtil.instantiateFacadeHelper(JDOMFacadeHelper.class.getName()); // The default class JMerger.DEFAULT_FACADE_HELPER_CLASS drops non Javadoc comments
               controlModel.initialize(facadeHelper, getStubbyMergeURI());
               JMerger merger = new JMerger(controlModel);
               merger.setSourceCompilationUnit(merger.createCompilationUnitForContents(content));
               merger.setTargetCompilationUnit(merger.createCompilationUnitForInputStream(stubJavaClass.getContents()));
               merger.merge();
               content = merger.getTargetCompilationUnitContents();
               // Modify file
               stubJavaClass.setContents(new ByteArrayInputStream(content.getBytes()), true, true, null);
            }
         }
      }
   }
   
   public static String getStubbyMergeURI() {
      Bundle bundle = Platform.getBundle(Activator.BUNDLE_ID);
      URL url = bundle.getEntry("jmerge/stubby-merge.xml");
      return url.toString();
   }

   /**
    * Extract Types and Members from an {@link ASTNode} and create a list of {@link Typ}
    * @param ast {@link ASTNode}
    * @return {@link List}of the found {@link Type} references.
    */
   public static List<AbstractType> extractTypesAndMembers(ASTNode ast) {
      final Map<String, AbstractType> types = new LinkedHashMap<String, AbstractType>();
      final List<AbstractType> outerTypes = new LinkedList<AbstractType>();
      if (ast != null) {
         ast.accept(new ASTVisitor() {
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
             * Proves if Member is a Variable, Method or Type an call special methods
             * @param binding {@ITypeBinding}
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
            
            private TypeVariable searchTypeVariable(List<TypeVariable> list, ITypeBinding typeBinding) {
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
             * Store a non-existing typenName in an Type
             * @param typeBinding The {@link ITypeBinding} to represent as {@link Type}.
             * @return The created {@link Type} if it does not exist before or a new created {@link Type} for the given name.
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
                     WildcardType wildcardType = createWildcardType(containerType, typeBinding);
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
                   
               
            private WildcardType createWildcardType(ITypeVariableContainer containerType, ITypeBinding typeBinding) {
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

            private Datatype createDataTyp(ITypeBinding typeBinding) {
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
            
            private ArrayType createArrayType(ITypeVariableContainer containerType, ITypeBinding typeBinding) {
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
            
            private GenericType createGenericType(ITypeVariableContainer containerType, ITypeBinding typeBinding) {
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

            private Type createType(ITypeVariableContainer containerType, ITypeBinding typeBinding) {
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
             * Creates Enum TypeKind for the Parameter Class, Interface, Annotation or Enum
             * @param typeBinding {@ITypeBinding}
             * @return Enum TypeKind
             */
            private TypeKind createKind(ITypeBinding typeBinding) {
                  if (typeBinding.isClass()){
                     return TypeKind.CLASS;
                  }
                  else if (typeBinding.isInterface()){
                     return TypeKind.INTERFACE;
                  }
                  else if (typeBinding.isAnnotation()){
                     return TypeKind.ANNOTATION;
                  }
                  else if (typeBinding.isEnum()){
                     return TypeKind.ENUM;
                  } else {
                     return null;
                  }
            }
            /**
             * Creates Enum Visibility with the parameter Public, Protected, Private or Default
             * @param modifiers {@int}
             * @return Enum Type Visibilty
             */
            private Visibility createVisibility(int modifiers) {
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
             * Store an non-existing Method in an Type
             * @param methodBinding {@IMethodBinding}
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
             * Store non existing Field in an Type
             * @param variableBinding {@IVariableBinding}
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
         });
         return outerTypes;
      }
      else {
         return null;
      }
   }

   protected static AbstractType findBaseType(AbstractType baseType) {
      while (baseType instanceof GenericType) {
         baseType = ((GenericType) baseType).getBaseType();
      }
      return baseType;
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
}
