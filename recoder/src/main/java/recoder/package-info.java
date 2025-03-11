/**
 * This package contains some basic definitions.
 * <p>
 * The central class of the RECODER system is {@link recoder.ServiceConfiguration}
 * which is responsible for maintaining all information repositories. A very
 * important repository is the {@link recoder.io.SourceFileRepository}, which
 * holds the set of known syntax trees. The construction of new syntax elements
 * lays in the responsibility of the {@link recoder.ProgramFactory} which also
 * allows access to a parser for the given language or language dialect.
 * Other repositories may know about additional abstractions or may
 * provide results derived by semantical analyses.
 * <p>
 * Besides of the base repositories, the package also contains some base
 * abstractions.
 * {@link recoder.ModelElement} is the parent of most other classes of the model.
 */
package recoder;
