/// Package holds utillities for working with proof script arguments.
/// The main functinoality is an injector, which maps named and positional arguments given in
/// [de.uka.ilkd.key.scripts.ScriptCommandAst] into JavaBeans. This includes correct type
/// conversions.
///
/// * Use [de.uka.ilkd.key.scripts.meta.Flag] to mark a boolean flag.
/// * Use [de.uka.ilkd.key.scripts.meta.Option] to mark a key-value argument.
/// * Use [de.uka.ilkd.key.scripts.meta.Argument] to mark a positional argument.
/// * Use [de.uka.ilkd.key.scripts.meta.PositionalVarargs] to catch-all positional arguments.
/// * Use [de.uka.ilkd.key.scripts.meta.OptionalVarargs] to catch-all key-value arguments with a
/// specific prefix.
///
///
/// @author Alexander Weigl
/// @version 1 (6/14/25)
@NullMarked
package de.uka.ilkd.key.scripts.meta;

import org.jspecify.annotations.NullMarked;
