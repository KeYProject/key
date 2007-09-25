package de.uka.ilkd.key.lang.clang.common.iface;

import java.math.BigInteger;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.lang.clang.common.sort.IClangObjectSort;
import de.uka.ilkd.key.lang.clang.common.sort.IClangValueSort;
import de.uka.ilkd.key.lang.clang.common.sort.object.IInstantiableObjectSort;
import de.uka.ilkd.key.lang.clang.common.sort.object.IStructuredSort;
import de.uka.ilkd.key.lang.clang.common.type.IClangInstantiableObjectType;
import de.uka.ilkd.key.lang.clang.common.type.IClangObjectType;
import de.uka.ilkd.key.lang.clang.common.type.IClangValueType;
import de.uka.ilkd.key.lang.clang.common.type.TypeBuilder;
import de.uka.ilkd.key.lang.clang.common.type.declaration.ArithmeticTypeDecl;
import de.uka.ilkd.key.lang.clang.common.type.declaration.StructDecl;
import de.uka.ilkd.key.lang.clang.common.type.object.ArrayType;
import de.uka.ilkd.key.lang.clang.common.type.object.ScalarType;
import de.uka.ilkd.key.lang.clang.common.type.object.StructType;
import de.uka.ilkd.key.lang.clang.common.type.object.VoidType;
import de.uka.ilkd.key.lang.clang.common.type.value.ArithmeticType;
import de.uka.ilkd.key.lang.clang.common.type.value.PointerType;

public abstract class BaseClangPlatform implements IClangPlatform {
        TypeBuilder typeBuilder;
        
        public BaseClangPlatform(TypeBuilder typeBuilder) {
                this.typeBuilder = typeBuilder;
        }

        public ArithmeticType getIntegerType(String id) {
                ArithmeticTypeDecl decl = typeBuilder.getArithmeticTypeDecl(id);
                if (decl != null)
                        return typeBuilder.getArithmeticType(decl);
                else
                        return null;
        }
        
        public KeYJavaType getIntegerTypePair(String id) {
                ArithmeticType type = getIntegerType(id);
                IClangValueSort sort = getIntegerSort(id);
                if (type != null && sort != null)
                        return new KeYJavaType(type, sort);
                else
                        return null;
        }
        
        public VoidType getVoidType() {
                return typeBuilder.getVoidType();
        }
        
        public KeYJavaType getVoidTypePair() {
                return new KeYJavaType(getVoidType(), getVoidSort()); 
        }
        
        public StructType getStructType(String id) {
                StructDecl decl = typeBuilder.getStructDecl(id);
                if (decl != null)
                        return typeBuilder.getStructType(decl);
                else
                        return null;
        }
        
        public KeYJavaType getStructTypePair(String id) {
                StructType type = getStructType(id);
                IStructuredSort sort = getStructSort(id);
                if (type != null && sort != null)
                        return new KeYJavaType(type, sort);
                else
                        return null;
        }
        
        public ScalarType getScalarType(IClangValueType valueType) {
                return typeBuilder.getScalarType(valueType);
        }
        
        public KeYJavaType getScalarTypePair(KeYJavaType typePair) {
                return new KeYJavaType(getScalarType((IClangValueType)typePair.getJavaType()), getScalarSort(typePair.getSort()));
        }
                
        public PointerType getPointerType(IClangObjectType type) {
                return typeBuilder.getPointerType(type);
        }
        
        public KeYJavaType getPointerTypePair(KeYJavaType typePair) {
                return new KeYJavaType(getPointerType((IClangObjectType)typePair.getJavaType()), getPointerSort((IClangObjectSort)typePair.getSort()));
        }
        
        public ArrayType getArrayType(IClangInstantiableObjectType type, BigInteger size) {
                return typeBuilder.getArrayType(type, size);
        }
        
        public KeYJavaType getArrayTypePair(KeYJavaType typePair, BigInteger size) {
                return new KeYJavaType(getArrayType((IClangInstantiableObjectType)typePair.getJavaType(), size), getArraySort((IInstantiableObjectSort)typePair.getSort(), size));
        }
}
