package de.uka.ilkd.key.lang.clang.common.type;

import java.math.BigInteger;

import junit.framework.TestCase;
import de.uka.ilkd.key.lang.clang.common.type.declaration.ArithmeticTypeDecl;
import de.uka.ilkd.key.lang.clang.common.type.declaration.StructDecl;
import de.uka.ilkd.key.lang.clang.common.type.object.ArrayType;
import de.uka.ilkd.key.lang.clang.common.type.object.ScalarType;
import de.uka.ilkd.key.lang.clang.common.type.object.StructType;
import de.uka.ilkd.key.lang.clang.common.type.value.ArithmeticType;
import de.uka.ilkd.key.lang.clang.common.type.value.PointerType;


/**
 * This class tests several methods of the TypeBuilder class.
 */
public class TestTypeBuilder extends TestCase {

        private TypeBuilder builder;
    
        public void setUp() {
                builder = new  TypeBuilder();
        }
        
        public void testArithmeticType() {
                ArithmeticTypeDecl decl1 = new ArithmeticTypeDecl("char");
                ArithmeticTypeDecl decl2 = new ArithmeticTypeDecl("int");
                builder.addArithmeticTypeDecl(decl1);
                builder.addArithmeticTypeDecl(decl2);
                
                boolean hadException = false;
                try {
                        builder.addArithmeticTypeDecl(decl1);
                }
                catch(Exception e) {
                        hadException = true;
                }
                assertTrue(     "Expecting exception on duplicate arithmetic type declaration",
                                hadException
                                );
                
                assertTrue(     "Looking up arithmetic type declaration \"char\"", 
                                builder.getArithmeticTypeDecl("char") == decl1
                                );
                assertTrue(     "Looking up arithmetic type declaration \"int\"", 
                                builder.getArithmeticTypeDecl("int") == decl2
                                );
                
                assertTrue(     "Expecting null when looking up non-existing arithmetic type declaration \"xxx\"",
                                builder.getArithmeticTypeDecl("xxx") == null                                
                                );
                
                ArithmeticType type1 = builder.getArithmeticType(decl1);
                assertTrue(     "Looking up arithmetic type for type declaration \"char\"",
                                type1 != null && type1.getDecl() == decl1);
                                
                ArithmeticType type2 = builder.getArithmeticType(decl2);
                assertTrue(     "Looking up arithmetic type for type declaration \"int\"",
                                type2 != null && type2.getDecl() == decl2);

                assertTrue(     "Expecting unique arithmetic type for type declaration \"char\"",
                                type1 == builder.getArithmeticType(decl1));                
        }
        
        public void testStruct() {
                StructDecl decl1 = new StructDecl("MyStruct1"); 
                StructDecl decl2 = new StructDecl("MyStruct2");                
                builder.addStructDecl(decl1);
                builder.addStructDecl(decl2);
                
                boolean hadException = false;
                try {
                        builder.addStructDecl(decl1);
                }
                catch(Exception e) {
                        hadException = true;
                }
                assertTrue(     "Expecting exception on duplicate struct declaration",
                                hadException
                                );
                
                assertTrue(
                                "Looking up structure declaration \"MyStruct1\"", 
                                builder.getStructDecl("MyStruct1") == decl1
                                );
                assertTrue(
                                "Looking up structure declaration \"MyStruct2\"", 
                                builder.getStructDecl("MyStruct2") == decl2
                                );                
                
                assertTrue(     "Expecting null when looking up non-existing struct declaration \"xxx\"",
                                builder.getStructDecl("xxx") == null                                
                                );
                
                StructType type1 = builder.getStructType(decl1);
                assertTrue(     "Looking up struct type for struct declaration \"MyStruct1\"",
                                type1 != null && type1.getDecl() == decl1);
                                
                StructType type2 = builder.getStructType(decl2);
                assertTrue(     "Looking up arithmetic type for type declaration \"MyStruct2\"",
                                type2 != null && type2.getDecl() == decl2);

                assertTrue(     "Expecting unique struct type for struct declaration \"MyStruct1\"",
                                type1 != null && type1 == builder.getStructType(decl1));                
                
        }
        
        public void testVoidType() {
                assertTrue(     "Expecting unique non-null instance of void type",
                                builder.getVoidType() != null & builder.getVoidType() == builder.getVoidType()
                                );
                                
        }
        
        public void testPointerType() {
                StructDecl structDecl = new StructDecl("MyStruct");
                builder.addStructDecl(structDecl);
                
                StructType structType= builder.getStructType(structDecl);
                PointerType type1 = builder.getPointerType(structType);
                assertTrue(     "Expecting pointer type with struct target type",
                                type1 != null && type1.getTargetType() == structType
                                );
                PointerType type2 = builder.getPointerType(structType);
                assertTrue(     "Expecting unique pointer type for given target type",
                                type2 != null && type2 == type1
                                );
        }
        
        public void testScalarType() {
                StructDecl structDecl = new StructDecl("MyStruct");
                builder.addStructDecl(structDecl);
                StructType structType= builder.getStructType(structDecl);
                PointerType ptrType = builder.getPointerType(structType);
                
                ScalarType type1 = builder.getScalarType(ptrType); 
                assertTrue(     "Expecting scalar type with struct pointer target type",
                                type1 != null && type1.getValueType() == ptrType
                                );
                ScalarType type2 = builder.getScalarType(ptrType); 
                assertTrue(     "Expecting unique pointer type for given value type",
                                type2 != null && type2 == type1
                                );
        }
        
        public void testArrayType() {
                StructDecl structDecl = new StructDecl("MyStruct");
                builder.addStructDecl(structDecl);
                StructType structType= builder.getStructType(structDecl);
                
                ArrayType type1 = builder.getArrayType(structType, new BigInteger("10")); 
                assertTrue(     "Expecting array type with struct element type",
                                type1 != null && type1.getElemType() == structType  && type1.getSize().equals(new BigInteger("10"))
                                );
                ArrayType type2 = builder.getArrayType(structType, new BigInteger("10")); 
                assertTrue(     "Expecting unique array type for given element type and size",
                                type2 != null && type2 == type1
                                );
        }

}
