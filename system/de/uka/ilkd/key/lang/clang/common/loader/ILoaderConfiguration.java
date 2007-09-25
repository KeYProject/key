package de.uka.ilkd.key.lang.clang.common.loader;

import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.programmeta.IClangProgramMeta;
import de.uka.ilkd.key.lang.clang.common.sort.object.MemberInfo;
import de.uka.ilkd.key.lang.clang.common.type.TypeBuilder;
import de.uka.ilkd.key.lang.common.programsv.ArrayOfBaseProgramSV;
import de.uka.ilkd.key.logic.Name;

/**
 * Loader configuration. Allows parametrizing possible implementations of CDL
 * sorts.
 * 
 * @author oleg.myrk@gmail.com
 */
public interface ILoaderConfiguration {
        /**
         * Returns current C language environment.
         * 
         * @return
         */
        IClangEnvironment getEnvironment();

        /**
         * Returns a C type builder.
         * 
         * @return
         */
        TypeBuilder getTypeBuilder();

        /**
         * A callback to manage C struct sort.
         * 
         * @author oleg.myrk@gmail.com
         */
        interface StructSortInfo {
                /**
                 * Wheter a struct was already registered.
                 * 
                 * @return
                 */
                boolean wasRegistered();

                /**
                 * Adds a new member to the struct sort.
                 * 
                 * @param info
                 */
                void addMember(MemberInfo info);

                /**
                 * Registers the struct sort. Should be called after all members
                 * have been added.
                 */
                void register();
        }

        /**
         * Returns struct sort callback.
         * 
         * @param id
         * @return
         */
        StructSortInfo getStructSortInfo(String id);

        /**
         * Returns program meta construct with given name, or <code>null</code>
         * if it does not exist.
         * 
         * @param name
         * @param arguments
         * @return
         */
        IClangProgramMeta getProgramMetaConstruct(Name name,
                        ArrayOfBaseProgramSV arguments);
}
