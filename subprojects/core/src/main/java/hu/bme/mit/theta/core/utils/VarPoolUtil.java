package hu.bme.mit.theta.core.utils;

import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.inttype.IntType;

import java.util.ArrayDeque;

import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

public class VarPoolUtil {

    private VarPoolUtil() {}

    private static ArrayDeque<VarDecl<IntType>> intPool=new ArrayDeque<VarDecl<IntType>>();
    private static int counter=0;

    public static VarDecl requestInt(){
        if(intPool.isEmpty()) return Decls.Var("temp"+counter++,Int());
        else return intPool.remove();
    }

    public static void returnInt(VarDecl<IntType> var){
        if(!intPool.contains(var)) intPool.addFirst(var);
    }

}
