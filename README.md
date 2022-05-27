# Blockaid

Blockaid is a system that enforces data-access policies for web applications.  It
interposes as a proxy between a web server and its backend SQL database, dynamically
verifies that queries issued by the web server comply with data-access
policies, and rejects non-compliant queries.

A data-access policy in Blockaid is specified as database view definitions (i.e., SQL
`SELECT` statement) that define what information in the database should be accessible to a user.
The view definitions may refer to request-specific parameters supplied by the
web application (e.g., the current user ID).
Here is an [example policy file](src/test/resources/DiasporaTest/policies.sql).
Given such a view-based privacy policy, Blockaid only allows SQL queries that
are guaranteed to reveal only information covered by the views.

For a more detailed description of the system, please refer to our [technical report](https://arxiv.org/abs/2205.06911).

Blockaid is being developed at the [Berkeley NetSys Lab](https://netsys.cs.berkeley.edu/).
If you have any questions, please contact Wen Zhang at zhangwen@cs.berkeley.edu.

## Usage

Blockaid is implemented as a JDBC driver and thus only works with
JVM-based applications (although its design does not preclude a standalone SQL
proxy implementation).  See [here](src/test/java/client/DiasporaTest.java)
for a usage example based on the [Diaspora](https://diasporafoundation.org/)
application.

Blockaid uses the [Apache Maven](https://maven.apache.org/index.html) build system,
which should take care of fetching all of Blockaid's dependencies _except_ Z3's Java binding.
We recommend downloading the Z3 distribution for your platform from its [release page](https://github.com/Z3Prover/z3/releases)
(see [pom.xml](pom.xml) for the required version -- currently, 4.8.12), and installing the jar with Maven like this:
```
$ mvn install:install-file \
   -Dfile=$Z3_DIR/com.microsoft.z3.jar \
   -DgroupId=com.microsoft \
   -DartifactId=z3 \
   -Dversion=4.8.12 \
   -Dpackaging=jar \
   -DgeneratePom=true
```
Make sure that Z3's native library is in the default library path (see [here](https://github.com/Z3Prover/z3/tree/master/examples/java)).

To check query compliance, Blockaid invokes SMT solver binaries:
`z3` ([Z3](https://github.com/Z3Prover/z3) v4.8.12), `cvc5` ([cvc5](https://cvc5.github.io/) v0.3), and `vampire` ([Vampire](https://vprover.github.io/) v4.6.1).
You should download the binaries and place them in a directory in the `PATH` environment/system variable.

