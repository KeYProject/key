package de.uka.ilkd.key.lang.clang.safe.sort;

import java.math.BigInteger;

import de.uka.ilkd.key.lang.clang.common.sort.object.IInstantiableObjectSort;
import de.uka.ilkd.key.lang.clang.safe.sort.object.ArrayMarkerSort;
import de.uka.ilkd.key.lang.clang.safe.sort.object.ObjectMarkerSort;
import de.uka.ilkd.key.lang.clang.safe.sort.object.ScalarSort;
import de.uka.ilkd.key.lang.clang.safe.sort.object.SizedArraySort;
import de.uka.ilkd.key.lang.clang.safe.sort.object.StructSort;
import de.uka.ilkd.key.lang.clang.safe.sort.object.UnsizedArraySort;
import de.uka.ilkd.key.lang.clang.safe.sort.object.VoidSort;
import de.uka.ilkd.key.lang.clang.safe.sort.value.IntegerSort;
import de.uka.ilkd.key.lang.clang.safe.sort.value.ValueMarkerSort;
import de.uka.ilkd.key.lang.common.services.ISymbolEnv;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Symbol builder provides services to add/create singleton instances of 
 * all CDL sorts. Logic sorts (boolean, int, null), arithmetic and structured sorts 
 * must be explicitly registered, while synthetic sorts (scalar, unsized/sized 
 * arrays) are created lazily when needed.
 * 
 * @author oleg.myrk@gmail.com
 */
public class SortBuilder {
        private final ISymbolEnv symbolEnv;
        private final Namespace sortNS;
        private final Namespace symbolNS;
        
        /**
         * Constructs symbol builder wrapping given parameters. One can create
         * arbitrary numbe of copies of symbol build with the same (or different)
         * parameters. 
         * 
         * @param symbolEnv
         */
        public SortBuilder(ISymbolEnv symbolEnv) {
                this.symbolEnv = symbolEnv;
                this.sortNS = symbolEnv.getSortNS();
                this.symbolNS = symbolEnv.getSymbolNS();
        }
        
        /**
         * Returns the symbol environment associated with this builder.
         * @return
         */
        public ISymbolEnv getSymbolEnv() {
                return symbolEnv;
        }
                
        /**
         * Returns sort namespace associated with this builder.
         * @return
         */
        public Namespace getSortNS() {
                return sortNS;
        }
        
        /**
         * Returns function namespace associated with this builder.
         * @return
         */
        public Namespace getFunctionNS() {
                return symbolNS;
        }
        
        /**
         * Returns the singleton boolean sort.
         * @return
         */
        public Sort getBooleanSort() {
                return symbolEnv.getBooleanSort();
        }
        
        /**
         * Returns the singleton int sort.
         * @return
         */
        public Sort getIntSort() {
                return symbolEnv.getIntSort();
        }
        
        /**
         * Returns the singleton Null sort.
         * @return
         */
        public Sort getNullSort() {
                return symbolEnv.getNullSort();                
        }

        /**
         * Initializes the namespaces with standard sorts.
         * @param symbolInfo
         */
        public void init() {
                // Prebuild marker sorts
                ValueMarkerSort valueMarkerSort = new ValueMarkerSort();
                sortNS.add(valueMarkerSort);
                valueMarkerSort.register(this);

                ObjectMarkerSort objectMarkerSort = new ObjectMarkerSort();
                sortNS.add(objectMarkerSort);
                objectMarkerSort.register(this);

                ArrayMarkerSort arrayMarkerSort = new ArrayMarkerSort(objectMarkerSort);
                sortNS.add(arrayMarkerSort);
                arrayMarkerSort.register(this);
                
                // Prebuild void sort
                VoidSort voidSort = new VoidSort(getObjectMarkerSort());
                sortNS.add(voidSort);
                voidSort.register(this);
        }
        
        /**
         * Registers a new arithmetic integer sort. Associated symbols are added to the namespace immediately.
         * @param id
         * @return
         */
        public IntegerSort registerIntegerSort(String id) {
                Name name = IntegerSort.formatName(id);
                
                if (sortNS.lookup(name) != null)
                        throw new IllegalArgumentException("Sort \"" + id +"\" already exists.");
                
                IntegerSort integerSort = new IntegerSort(id, symbolEnv.getIntSort(), getValueMarkerSort());
                sortNS.add(integerSort);
                integerSort.register(this);
                
                return integerSort;
        }
        
        /**
         * Preregisters a new struct sort. The sort appears immediately in the namespace afeter calling this method.
         * Make sure You call {@link #registerStructSort()} after all sorts this struct sort depends on are at 
         * least preregistered/lazily created. This will add to the namespace associated symbols. We need such 
         * approach because of cyclic dependencies between structured types. Do not preregister the same struct
         * more than once.
         * 
         * @param id
         * @return
         */
        public StructSort preregisterStructSort(String id) {
                Name name = StructSort.formatName(id);
                if (sortNS.lookup(name) != null)
                        throw new IllegalArgumentException("Struct sort \"" + id +"\" already exists.");

                StructSort structSort = new StructSort(id, getObjectMarkerSort(), getVoidSort());
                sortNS.add(structSort);                
                return structSort;
        }
        
        /**
         * Registers previously preregistered struct sort. Should be called 
         * exactly once for each struct sort. The associated symbols appear  
         * in the namespace set only after this method is called.
         *    
         * @param structSort
         */
        public void registerStructSort(String id) {
                Name name = StructSort.formatName(id);
                
                StructSort structSort = (StructSort)sortNS.lookup(name);
                if (structSort == null)
                        throw new IllegalArgumentException("Struct sort with id \"" + id + "\" does not exist");
                structSort.register(this);
        }
        
        /**
         * Returns the singleton value marker sort.
         * 
         * @return
         */
        public ValueMarkerSort getValueMarkerSort() {
                return (ValueMarkerSort)sortNS.lookup(ValueMarkerSort.formatName());
        }        
        
        /**
         * Returns the singleton object marker sort.
         * @return
         */
        public ObjectMarkerSort getObjectMarkerSort() {
                return (ObjectMarkerSort)sortNS.lookup(ObjectMarkerSort.formatName());
        }        
        
        /**
         * Returns the singleton array marker sort.
         * @return
         */
        public ArrayMarkerSort getArrayMarkerSort() {
                return (ArrayMarkerSort)sortNS.lookup(ArrayMarkerSort.formatName());
        }
        
        /**
         * Returns the singleton void sort.
         * @return
         */
        public VoidSort getVoidSort() {
                return (VoidSort)sortNS.lookup(VoidSort.formatName());
        }
        
        /**
         * Looks up arithemtic integer sort by its id. 
         * @param id
         * @return arithemtic integer sort or <code>null</code>, if not present
         */
        public IntegerSort getIntegerSort(String id) {
                return (IntegerSort)sortNS.lookup(IntegerSort.formatName(id));
        }        
        
        /**
         * Looks up struct sort by its id.
         * @param id
         * @return struct sort or <code>null</code>, if not present
         */
        public StructSort getStructSort(String id) {
                return (StructSort)sortNS.lookup(StructSort.formatName(id));
        }

        /**
         * Returns (and possible creates) the singleton scalar sort for the given singleton value sort. 
         * The namespace set is populated with associated symbols.
         * @param valueSort
         * @return
         */        
        public ScalarSort getScalarSort(Sort valueSort) {
                ScalarSort sort = (ScalarSort)sortNS.lookup(ScalarSort.formatName(valueSort));
                if (sort == null) {
                        sort = new ScalarSort(valueSort, getObjectMarkerSort(), getVoidSort());
                        sortNS.add(sort);
                        sort.register(this);
                }
                return sort;
        }
        
        /**
         * Returns (and possibly creates) the singleton unsized array sort for the given singleton element sort. 
         * The namespace set is populated immediately.
         * @param elemSort
         * @return
         */        
        public UnsizedArraySort getUnsizedArraySort(IInstantiableObjectSort elemSort) {
                UnsizedArraySort sort = (UnsizedArraySort)sortNS.lookup(UnsizedArraySort.formatName(elemSort));
                if (sort == null) {
                        sort = new UnsizedArraySort(elemSort, getObjectMarkerSort(), getArrayMarkerSort(), getVoidSort());
                        sortNS.add(sort);
                        sort.register(this);
                }
                return sort;
        }

        /**
         * Returns the singleton sized array sort for the given singleton element sort and size.
         * The namespace set is populated immediately (after the logic sorts are resolved).
         * @param elemSort
         * @param size
         * @return
         */        
        public SizedArraySort getSizedArraySort(IInstantiableObjectSort elemSort, BigInteger size) {
                SizedArraySort sort = (SizedArraySort)sortNS.lookup(SizedArraySort.formatName(elemSort, size));
                if (sort == null) {
                        sort = new SizedArraySort(getUnsizedArraySort(elemSort), size);
                        sortNS.add(sort);
                        sort.register(this);
                }
                return sort;
        }
}
