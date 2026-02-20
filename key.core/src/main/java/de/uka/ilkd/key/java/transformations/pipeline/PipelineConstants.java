/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.transformations.pipeline;

import static de.uka.ilkd.key.logic.JavaDLFieldNames.IMPLICIT_NAME_PREFIX;

/**
 * @author Alexander Weigl
 * @version 1 (11/6/21)
 */
public interface PipelineConstants {
    String CONSTRUCTOR_NORMALFORM_IDENTIFIER = IMPLICIT_NAME_PREFIX + "init";
    String OBJECT_INITIALIZER_IDENTIFIER = IMPLICIT_NAME_PREFIX + "objectInitializer";
    String IMPLICIT_CLASS_PREPARED = IMPLICIT_NAME_PREFIX + "classPrepared";
    String IMPLICIT_CLASS_INITIALIZED = IMPLICIT_NAME_PREFIX + "classInitialized";
    String IMPLICIT_CLASS_INIT_IN_PROGRESS = IMPLICIT_NAME_PREFIX + "classInitializationInProgress";
    String IMPLICIT_CLASS_ERRONEOUS = IMPLICIT_NAME_PREFIX + "classErroneous";
    String IMPLICIT_CREATED = IMPLICIT_NAME_PREFIX + "created";
    String IMPLICIT_INITIALIZED = IMPLICIT_NAME_PREFIX + "initialized";
    String IMPLICIT_TRANSIENT = IMPLICIT_NAME_PREFIX + "transient";
    String IMPLICIT_TRANSACTION_UPDATED = IMPLICIT_NAME_PREFIX + "transactionConditionallyUpdated";
    String IMPLICIT_ENCLOSING_THIS = IMPLICIT_NAME_PREFIX + "enclosingThis";
    String FINAL_VAR_PREFIX = "_outer_final_";
    String VIRTUAL_METHOD_FOR_PARSING = IMPLICIT_NAME_PREFIX + "virtual_method_for_parsing";
    String VIRTUAL_CLASS_FOR_PARSING = IMPLICIT_NAME_PREFIX + "virtual_class_for_parsing";
    String IMPLICIT_OBJECT_PREPARE = IMPLICIT_NAME_PREFIX + "prepare";
    String IMPLICIT_OBJECT_PREPARE_ENTER = IMPLICIT_NAME_PREFIX + "prepareEnter";
    String IMPLICIT_INSTANCE_ALLOCATE = IMPLICIT_NAME_PREFIX + "allocate";
}
