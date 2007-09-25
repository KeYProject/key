package de.uka.ilkd.key.lang.clang.safe.sort;

import java.math.BigInteger;

import junit.framework.TestCase;
import de.uka.ilkd.key.lang.clang.common.sort.object.IArraySort;
import de.uka.ilkd.key.lang.clang.common.sort.object.IScalarSort;
import de.uka.ilkd.key.lang.clang.common.sort.object.MemberInfo;
import de.uka.ilkd.key.lang.clang.common.sort.value.IArithmeticSort;
import de.uka.ilkd.key.lang.clang.safe.sort.object.MemberFunction;
import de.uka.ilkd.key.lang.clang.safe.sort.object.ScalarSort;
import de.uka.ilkd.key.lang.clang.safe.sort.object.SizedArraySort;
import de.uka.ilkd.key.lang.clang.safe.sort.object.StructSort;
import de.uka.ilkd.key.lang.clang.safe.sort.object.UnsizedArraySort;
import de.uka.ilkd.key.lang.clang.safe.sort.value.ArithmeticSort;
import de.uka.ilkd.key.lang.common.services.ISymbolEnv;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.RigidFunction;
import de.uka.ilkd.key.logic.sort.NullSort;
import de.uka.ilkd.key.logic.sort.NullSortImpl;
import de.uka.ilkd.key.logic.sort.PrimitiveSort;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * This class tests several methods of the SortBuilder class.
 */
public class TestSortBuilder extends TestCase {

        private SortBuilder sortBuilder;
        private Namespace sortNS;
        private Namespace symbolNS;
            
        public void setUp() {
                sortNS = new Namespace();
                symbolNS = new Namespace();

                final PrimitiveSort  booleanSort = new PrimitiveSort(new Name("boolean"));                
                final PrimitiveSort intSort = new PrimitiveSort(new Name("int"));
                final NullSort nullSort = new NullSortImpl(new Name("Null"));
                final Function nullConstant = new RigidFunction(new Name("null"), nullSort, new Sort[0]);
                
                sortNS.add(booleanSort);
                sortNS.add(intSort);
                sortNS.add(nullSort);
                symbolNS.add(nullConstant);
                
                final ISymbolEnv symbolEnv = new ISymbolEnv() {
                        public Namespace getSortNS() {
                                return sortNS;
                        }
                        
                        public Namespace getSymbolNS() {
                                return symbolNS;
                        }
                        
                        public Sort getBooleanSort() {
                                return booleanSort;
                        }
                        
                        public Sort getIntSort() {
                                return intSort;
                        }
                        
                        public Sort getNullSort() {
                                return nullSort;
                        }
                        
                        public Function getNullConstant() {
                                return nullConstant;
                        }
                        
                        public Junctor getAndJunctor() {
                                throw new RuntimeException("Not supported in this unit test!");
                        }                
                        
                        public Junctor getOrJunctor() {
                                throw new RuntimeException("Not supported in this unit test!");
                                
                        }
                        
                        public Junctor getNotJunctor() {
                                throw new RuntimeException("Not supported in this unit test!");
                        }
                        
                        public Junctor getTrueJunctor() {
                                throw new RuntimeException("Not supported in this unit test!");
                        }

                        public Junctor getFalseJunctor() {
                                throw new RuntimeException("Not supported in this unit test!");
                        }
                        
                        public Term encodeInteger(BigInteger integer) {
                                throw new RuntimeException("Not supported in this unit test!");
                        }
                        
                        public BigInteger parseInteger(Term term) {
                                throw new RuntimeException("Not supported in this unit test!");
                        }
                        
                        public Function getLessFunction() {
                                throw new RuntimeException("Not supported in this unit test!");
                        }
                        
                        public Function getLessEqFunction() {
                                throw new RuntimeException("Not supported in this unit test!");
                        }
                        
                        public Function getGreaterFunction() {
                                throw new RuntimeException("Not supported in this unit test!");
                        }
                        
                        public Function getGreaterEqFunction() {
                                throw new RuntimeException("Not supported in this unit test!");
                        }                        
                };
                
                sortBuilder = new SortBuilder(symbolEnv);
                sortBuilder.init();
        }
        
        public void testMarkerSorts() {
                assertTrue(     "Expecting singleton value marker sort",
                                sortBuilder.getValueMarkerSort() != null &&
                                sortBuilder.getValueMarkerSort() == sortBuilder.getValueMarkerSort());
                
                assertTrue(     "Expecting singleton object marker sort",
                                sortBuilder.getObjectMarkerSort() != null &&
                                sortBuilder.getObjectMarkerSort() == sortBuilder.getObjectMarkerSort());
                
                assertTrue(     "Expecting singleton array marker sort",
                                sortBuilder.getArrayMarkerSort() != null &&
                                sortBuilder.getArrayMarkerSort() == sortBuilder.getArrayMarkerSort());
                
                assertTrue(     "Sorts should be added to the namespace set",
                                sortNS.lookup(sortBuilder.getValueMarkerSort().name()) == sortBuilder.getValueMarkerSort()); 

                assertTrue(     "Sorts symbols should refer to their parent",
                                sortBuilder.getValueMarkerSort().getIsValidValPredicate().getValueMarkerSort() == sortBuilder.getValueMarkerSort());

                assertTrue(     "Sorts symbols should be added to the namespace set",
                                sortBuilder.getValueMarkerSort().getIsValidValPredicate() != null &&
                                symbolNS.lookup(sortBuilder.getValueMarkerSort().getIsValidValPredicate().name()) == sortBuilder.getValueMarkerSort().getIsValidValPredicate());                
                
                assertTrue(     "Sorts should be added to the namespace set",
                                sortNS.lookup(sortBuilder.getObjectMarkerSort().name()) == sortBuilder.getObjectMarkerSort()); 

                assertTrue(     "Sorts symbols should refer to their parent",
                                sortBuilder.getObjectMarkerSort().getIsValidPtrPredicate().getObjectMarkerSort() == sortBuilder.getObjectMarkerSort());

                assertTrue(     "Sorts symbols should be added to the namespace set",
                                sortBuilder.getObjectMarkerSort().getIsValidPtrPredicate() != null &&
                                symbolNS.lookup(sortBuilder.getObjectMarkerSort().getIsValidPtrPredicate().name()) == sortBuilder.getObjectMarkerSort().getIsValidPtrPredicate());                
                
                assertTrue(     "Sorts should be added to the namespace set",
                                sortNS.lookup(sortBuilder.getValueMarkerSort().name()) == sortBuilder.getValueMarkerSort()); 

                assertTrue(     "Sorts symbols should refer to their parent",
                                sortBuilder.getArrayMarkerSort().getSizeFunction().getArrayMarkerSort() == sortBuilder.getArrayMarkerSort());

                assertTrue(     "Sorts symbols should be added to the namespace set after resolving",
                                sortBuilder.getArrayMarkerSort().getSizeFunction() != null &&
                                symbolNS.lookup(sortBuilder.getArrayMarkerSort().getSizeFunction().name()) == sortBuilder.getArrayMarkerSort().getSizeFunction());                
        }
        
        public void testArithmeticSort() {               
                ArithmeticSort sort1 = sortBuilder.registerIntegerSort("XCHAR"); 
                IArithmeticSort sort2 = sortBuilder.registerIntegerSort("XSINT");
                
                boolean hadException = false;
                try {
                        sortBuilder.registerIntegerSort("XCHAR");
                }
                catch(Exception e) {
                        hadException = true;
                }
                assertTrue(     "Expecting exception on duplicate arithmetic sort registration",
                                hadException);

                assertTrue(     "Looking up unique arithemtic sort \"XCHAR\"",
                                sortBuilder.getIntegerSort("XCHAR") == sort1);
                                
                assertTrue(     "Looking up unique arithemtic sort \"XSINT\"",
                                sortBuilder.getIntegerSort("XSINT") == sort2);
                
                assertTrue(     "Expecting null when looking up non-existing arithmetic sort \"xxx\"",
                                sortBuilder.getIntegerSort("xxx") == null);
                
                assertTrue(     "Sorts should be added to the namespace set",
                                sortNS.lookup(sort1.name()) == sort1);
        }
        
        
        public void testStructSort() {
                StructSort sort1 = sortBuilder.preregisterStructSort("MyStruct1"); 
                StructSort sort2 = sortBuilder.preregisterStructSort("MyStruct2");
                
                boolean hadException = false;
                try {
                        sortBuilder.preregisterStructSort("MyStruct1");
                }
                catch(Exception e) {
                        hadException = true;
                }
                assertTrue(     "Expecting exception on duplicate struct sort registration",
                                hadException);

                assertTrue(     "Looking up unique arithemtic sort \"MyStruct1\"",
                                sortBuilder.getStructSort("MyStruct1") == sort1);
                                
                assertTrue(     "Looking up unique arithemtic sort \"MyStruct2\"",
                                sortBuilder.getStructSort("MyStruct2") == sort2);
                
                assertTrue(     "Expecting null when looking up non-existing struct sort \"xxx\"",
                                sortBuilder.getStructSort("xxx") == null);
                
                assertTrue(     "Struct sort should be added to the namespace set after preregistering",
                                sortNS.lookup(sort1.name()) == sort1);
                
                sort1.getMemberInfoMap().put("member", new MemberInfo("member", sort2, 1));
                
                sortBuilder.registerStructSort("MyStruct1");
        
                assertTrue(     "Struct sort member functions should be created after registering the sort",                                        
                                sort1.getMemberFunctionMap() != null && 
                                sort1.getMemberFunctionMap().get("member") != null);                
                
                MemberFunction memberFunction = sort1.getMemberFunctionMap().get("member");
                assertTrue(     "Struct sort member functions should be added to the namespace set after registering the sort",
                                symbolNS.lookup(memberFunction.name()) == memberFunction);

                assertTrue(     "Sorts symbols should refer to their parent",
                                memberFunction.getStructuredSort() == sort1);
                
                assertTrue(     "Instantiable sort repository function should be created  after registering",                                        
                                sort1.getRepositoryFunction() != null);                
               
                assertTrue(     "Instantiable sort repository function should be added to the namespace set after registering",
                                symbolNS.lookup(sort1.getRepositoryFunction().name()) == sort1.getRepositoryFunction());

                assertTrue(     "Sorts symbols should refer to their parent",
                                sort1.getRepositoryFunction().getInstantiableObjectSort() == sort1);        
        }
                
        public void testVoidSort() {
                assertTrue(     "Expecting singleton void sort",
                                sortBuilder.getVoidSort() != null &&
                                sortBuilder.getVoidSort() == sortBuilder.getVoidSort());
                
                assertTrue(     "Sorts should be added to the namespace set",
                                sortNS.lookup(sortBuilder.getVoidSort().name()) == sortBuilder.getVoidSort()); 
        }
        
        public void testScalarSort() {
                ArithmeticSort arithmSort1 = sortBuilder.registerIntegerSort("XCHAR"); 
                ArithmeticSort arithmSort2 = sortBuilder.registerIntegerSort("XSINT");
                
                ScalarSort sort1 = sortBuilder.getScalarSort(arithmSort1);
                IScalarSort sort2 = sortBuilder.getScalarSort(arithmSort2);
                
                assertTrue(     "Expecting the right value sort",
                                sort1.getValueSort() == arithmSort1);
                
                assertTrue(     "Looking up unique scalar sort",
                                sortBuilder.getScalarSort(arithmSort1) == sort1);
                
                assertTrue(     "Expecting the right value sort",
                                sort2.getValueSort() == arithmSort2);
                
                assertTrue(     "Looking up unique scalar sort",
                                sortBuilder.getScalarSort(arithmSort2) == sort2);

                assertTrue(     "Scalar sort should be added to the namespace set",
                                sortNS.lookup(sort1.name()) == sort1);
                
                assertTrue(     "Scalar sort value location should be created",                                        
                                sort1.getValueLocation() != null);                
               
                assertTrue(     "Scalar sort value location should be added to the namespace set",
                                symbolNS.lookup(sort1.getValueLocation().name()) == sort1.getValueLocation());
                
                assertTrue(     "Instantiable sort repository function should be created",                                        
                                sort1.getRepositoryFunction() != null);                
               
                assertTrue(     "Instantiable sort repository function should be added to the namespace set",
                                symbolNS.lookup(sort1.getRepositoryFunction().name()) == sort1.getRepositoryFunction());

                assertTrue(     "Sorts symbols should refer to their parent",
                                sort1.getRepositoryFunction().getInstantiableObjectSort() == sort1);        
        }
        
        public void testUnsizedArraySort() {
                ArithmeticSort arithmSort1 = sortBuilder.registerIntegerSort("XCHAR");
                ArithmeticSort arithmSort2 = sortBuilder.registerIntegerSort("XSINT");

                ScalarSort scalarSort1 = sortBuilder.getScalarSort(arithmSort1);
                ScalarSort scalarSort2 = sortBuilder.getScalarSort(arithmSort2);
                
                UnsizedArraySort sort1 = sortBuilder.getUnsizedArraySort(scalarSort1);
                UnsizedArraySort sort2 = sortBuilder.getUnsizedArraySort(scalarSort2);
                
                assertTrue(     "Expecting the right element sort",
                                sort1.getElemSort() == scalarSort1);
                
                assertTrue(     "Looking up unique unsized array sort",
                                sortBuilder.getUnsizedArraySort(scalarSort1) == sort1);
                
                assertTrue(     "Expecting the right element sort",
                                sort2.getElemSort() == scalarSort2);
                
                assertTrue(     "Looking up unique unsized array sort",
                                sortBuilder.getUnsizedArraySort(scalarSort2) == sort2);

                assertTrue(     "Unsized array should be added to the namespace set",
                                sortNS.lookup(sort1.name()) == sort1);
                
                assertTrue(     "Unsized array sort elem function should be created",                                        
                                sort1.getElemFunction() != null);                
               
                assertTrue(     "Unsized array sort elem function should be added to the namespace set",
                                symbolNS.lookup(sort1.getElemFunction().name()) == sort1.getElemFunction());
                
                assertTrue(     "Instantiable sort repository function should be created",                                        
                                sort1.getRepositoryFunction() != null);                
               
                assertTrue(     "Instantiable sort repository function should be added to the namespace set",
                                symbolNS.lookup(sort1.getRepositoryFunction().name()) == sort1.getRepositoryFunction());

                assertTrue(     "Sorts symbols should refer to their parent",
                                sort1.getRepositoryFunction().getUnsizedArraySort() == sort1);        
        }
        
        public void testSizedArraySort() {
                ArithmeticSort arithmSort1 = sortBuilder.registerIntegerSort("XCHAR");
                ArithmeticSort arithmSort2 = sortBuilder.registerIntegerSort("XSINT");

                ScalarSort scalarSort1 = sortBuilder.getScalarSort(arithmSort1);
                ScalarSort scalarSort2 = sortBuilder.getScalarSort(arithmSort2);
                
                SizedArraySort sort1 = sortBuilder.getSizedArraySort(scalarSort1, new BigInteger("10"));
                IArraySort sort2 = sortBuilder.getSizedArraySort(scalarSort2, new BigInteger("20"));
                
                assertTrue(     "Expecting the right element sort",
                                sort1.getElemSort() == scalarSort1);
                
                assertTrue(     "Looking up unique unsized array sort",
                                sortBuilder.getSizedArraySort(scalarSort1, new BigInteger("10")) == sort1);
                
                assertTrue(     "Expecting the right element sort",
                                sort2.getElemSort() == scalarSort2);
                
                assertTrue(     "Looking up unique unsized array sort",
                                sortBuilder.getSizedArraySort(scalarSort2, new BigInteger("20")) == sort2);

                assertTrue(     "Sized array should be added to the namespace set",
                                sortNS.lookup(sort1.name()) == sort1);
                
                assertTrue(     "Instantiable sort repository function should be created",                                        
                                sort1.getRepositoryFunction() != null);                
               
                assertTrue(     "Instantiable sort repository function should be added to the namespace set",
                                symbolNS.lookup(sort1.getRepositoryFunction().name()) == sort1.getRepositoryFunction());

                assertTrue(     "Sorts symbols should refer to their parent",
                                sort1.getRepositoryFunction().getInstantiableObjectSort() == sort1);        
        }
                
}
