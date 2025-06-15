/// This package contains the classes and interfaces to create the external SMT solver processes and
/// communicate with them:
///
/// - [de.uka.ilkd.key.smt.communication.ExternalProcessLauncher] creates and starts the
/// external process and connects it to the pipe.
/// - [de.uka.ilkd.key.smt.communication.Pipe] is responsible for sending and receiving
/// input/output strings to/from the external process. It uses
/// [de.uka.ilkd.key.smt.communication.BufferedMessageReader] to split the received strings
/// into separate messages.
/// - [de.uka.ilkd.key.smt.communication.AbstractSolverSocket] defines the (solver specific)
/// behaviour for handling solver results.
/// - [de.uka.ilkd.key.smt.communication.SolverCommunication] stores the messages sent to and
/// from the external solver.
///
@NullMarked
package de.uka.ilkd.key.smt.communication;

import org.jspecify.annotations.NullMarked;
