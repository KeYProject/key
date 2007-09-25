package de.uka.ilkd.key.lang.clang.common.type;

import java.math.BigInteger;

import de.uka.ilkd.key.lang.clang.common.type.declaration.ArithmeticTypeDecl;
import de.uka.ilkd.key.lang.clang.common.type.declaration.HashMapFromStringToArithmeticTypeDecl;
import de.uka.ilkd.key.lang.clang.common.type.declaration.HashMapFromStringToStructDecl;
import de.uka.ilkd.key.lang.clang.common.type.declaration.StructDecl;
import de.uka.ilkd.key.lang.clang.common.type.object.ArrayType;
import de.uka.ilkd.key.lang.clang.common.type.object.ScalarType;
import de.uka.ilkd.key.lang.clang.common.type.object.StructType;
import de.uka.ilkd.key.lang.clang.common.type.object.VoidType;
import de.uka.ilkd.key.lang.clang.common.type.value.ArithmeticType;
import de.uka.ilkd.key.lang.clang.common.type.value.PointerType;

/**
 * A builder that allows creating singleton instances of all possible C types 
 * (pointers, arrays, etc). Atomic types (arithmetic, structs, etc) are 
 * represented by a type declaration that has to be registered by its 
 * identifer and the type itself that references the declaration. 
 * 
 * Types are split into value (suitable for an rvalue) and object 
 * (suitable for an lvalue) types. Type <code>void</code> is considered
 * to be an object type.
 * 
 * When calling methods returning singletons, the arguments passed must also
 * be singletons. Creating type singletons is based on the properties of 
 * {@linke IType.equal()}.
 *   
 * @author oleg.myrk@gmail.com
 */
public class TypeBuilder {
        /**
         * Arithemtic declarations indexed by their ids.
         */
        private HashMapFromStringToArithmeticTypeDecl arithmeticTypeDeclMap = new HashMapFromStringToArithmeticTypeDecl();

        /**
         * Struct declarations indexed by their ids.
         */
        private HashMapFromStringToStructDecl structDeclMap = new HashMapFromStringToStructDecl();
        
        /**
         * A lazily populated set of types. Represented as a HashMap<K,K> becase there was no HashSet<K,K>.
         */
        private HashMapFromIClangTypeToIClangType types = new HashMapFromIClangTypeToIClangType();
        
        public TypeBuilder() {
                arithmeticTypeDeclMap = new HashMapFromStringToArithmeticTypeDecl();
                structDeclMap = new HashMapFromStringToStructDecl();
                types = new HashMapFromIClangTypeToIClangType();                
        }
        
        private TypeBuilder(
                        HashMapFromStringToArithmeticTypeDecl arithmeticTypeDeclMap,
                        HashMapFromStringToStructDecl structDeclMap,
                        HashMapFromIClangTypeToIClangType types
                        ) {
                this.arithmeticTypeDeclMap = arithmeticTypeDeclMap;
                this.structDeclMap = structDeclMap;
                this.types = types;
        }
        
        public TypeBuilder copy() {
                return new TypeBuilder(
                                (HashMapFromStringToArithmeticTypeDecl)arithmeticTypeDeclMap.clone(),
                                (HashMapFromStringToStructDecl)structDeclMap.clone(),
                                (HashMapFromIClangTypeToIClangType)types.clone()
                                );
        }
        
        /**
         * Adds a new arithmetic type declaration.
         * @param typeDecl
         */
        public void addArithmeticTypeDecl(ArithmeticTypeDecl typeDecl) {
                if (arithmeticTypeDeclMap.containsKey(typeDecl.getId()))
                        throw new IllegalArgumentException("Arithmetic type declaration \"" + typeDecl.getId() +"\" already exists.");
                arithmeticTypeDeclMap.put(typeDecl.getId(), typeDecl);
        }

        /**
         * Adds a new struct declaration.
         * @param typeDecl
         */
        public void addStructDecl(StructDecl typeDecl) {
                if (structDeclMap.containsKey(typeDecl.getId()))
                        throw new IllegalArgumentException("Struct declaration \"" + typeDecl.getId() +"\" already exists.");
                structDeclMap.put(typeDecl.getId(), typeDecl);
        }

        /**
         * Looks up arithemtic type declaration by its id.
         * @param id
         * @return arithemtic type declaration or <code>null</code>, if not present
         */
        public ArithmeticTypeDecl getArithmeticTypeDecl(String id) {
                return arithmeticTypeDeclMap.get(id);
        }
        
        /**
         * Looks up struct declaration by its id.
         * @param id
         * @return struct declaration or <code>null</code>, if not present
         */        
        public StructDecl getStructDecl(String id) {
                return structDeclMap.get(id);
        }

        /**
         * Returns the singleton void type.
         * @return
         */
        public VoidType getVoidType() {
                return (VoidType)getSingletonType(new VoidType());
        }
        

        /**
         * Returns the singleton arithmetic type for the given arithmetic type declaration.
         * @param typeDecl
         * @return
         */
        public ArithmeticType getArithmeticType(ArithmeticTypeDecl typeDecl) {
                return (ArithmeticType)getSingletonType(new ArithmeticType(typeDecl));
        }

        /**
         * Returns the singleton struct type for the given struct type declaration.
         * @param typeDecl
         * @return
         */
        public StructType getStructType(StructDecl typeDecl) {
                return (StructType)getSingletonType(new StructType(typeDecl));
        }        

        /**
         * Returns the singleton pointer type for the given singleton target type.
         * @param targetType
         * @return
         */
        public PointerType getPointerType(IClangObjectType targetType) {
                return (PointerType)getSingletonType(new PointerType(targetType));
        }

        /**
         * Returns the singleton scalar type for the given singleton value type.
         * @param valueType
         * @return
         */
        public ScalarType getScalarType(IClangValueType valueType) {
                return (ScalarType)getSingletonType(new ScalarType(valueType));
        }        

        /**
         * Returns the singleton array type for the given singleton element type and size.
         * @param elemType
         * @param size
         * @return
         */
        public ArrayType getArrayType(IClangInstantiableObjectType elemType, BigInteger size) {
                return (ArrayType)getSingletonType(new ArrayType(elemType, size));
        }        

        /**
         * Returns the singleton instance of {@link IClangType} which is equal to the blueprint.
         * If such type is not present yet, the blueprint becomes the singleton.
         * The types referenced by the blueprint must be also singletons.  
         * @param blueprint type blueprint
         * @return singleton equal to the blueprint, or the blueprint itself, if there was no singleton
         */
        private IClangType getSingletonType(IClangType blueprint) {
                IClangType type = types.get(blueprint);
                if (type == null) {
                        types.put(blueprint, blueprint);
                        return blueprint;
                }
                else
                        return type;
        }
}
