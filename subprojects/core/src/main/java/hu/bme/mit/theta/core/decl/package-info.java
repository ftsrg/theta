/**
 * This package contains the different declarations.
 * - {@link hu.bme.mit.theta.core.decl.ConstDecl} represents a constant that can be directly
 *   handled by the SMT solvers.
 * - {@link hu.bme.mit.theta.core.decl.VarDecl} represents a variable, that can have multiple
 *   associated {@link hu.bme.mit.theta.core.decl.ConstDecl}s for each index (e.g. in a path)
 * - {@link hu.bme.mit.theta.core.decl.ParamDecl} represents a parameter declaration.
 *
 * Use the factory class {@link hu.bme.mit.theta.core.decl.Decls} to instantiate them.
 */

package hu.bme.mit.theta.core.decl;