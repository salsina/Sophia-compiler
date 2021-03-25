package main.visitor.codeGenerator;

import com.sun.jdi.BooleanType;
import com.sun.source.tree.TryTree;
import main.ast.nodes.Program;
import main.ast.nodes.declaration.classDec.ClassDeclaration;
import main.ast.nodes.declaration.classDec.classMembersDec.ConstructorDeclaration;
import main.ast.nodes.declaration.classDec.classMembersDec.FieldDeclaration;
import main.ast.nodes.declaration.classDec.classMembersDec.MethodDeclaration;
import main.ast.nodes.declaration.variableDec.VarDeclaration;
import main.ast.nodes.expression.*;
import main.ast.nodes.expression.operators.BinaryOperator;
import main.ast.nodes.expression.operators.UnaryOperator;
import main.ast.nodes.expression.values.ListValue;
import main.ast.nodes.expression.values.NullValue;
import main.ast.nodes.expression.values.primitive.BoolValue;
import main.ast.nodes.expression.values.primitive.IntValue;
import main.ast.nodes.expression.values.primitive.StringValue;
import main.ast.nodes.statement.*;
import main.ast.nodes.statement.loop.BreakStmt;
import main.ast.nodes.statement.loop.ContinueStmt;
import main.ast.nodes.statement.loop.ForStmt;
import main.ast.nodes.statement.loop.ForeachStmt;
import main.ast.types.NullType;
import main.ast.types.Type;
import main.ast.types.functionPointer.FptrType;
import main.ast.types.list.ListNameType;
import main.ast.types.list.ListType;
import main.ast.types.single.BoolType;
import main.ast.types.single.ClassType;
import main.ast.types.single.IntType;
import main.ast.types.single.StringType;
import main.symbolTable.SymbolTable;
import main.symbolTable.exceptions.ItemNotFoundException;
import main.symbolTable.items.ClassSymbolTableItem;
import main.symbolTable.items.FieldSymbolTableItem;
import main.symbolTable.items.MethodSymbolTableItem;
import main.symbolTable.utils.graph.Graph;
import main.visitor.Visitor;
import main.visitor.typeChecker.ExpressionTypeChecker;

import java.io.*;
import java.lang.reflect.Field;
import java.util.ArrayList;

public class CodeGenerator extends Visitor<String> {
    ExpressionTypeChecker expressionTypeChecker;
    Graph<String> classHierarchy;
    private String outputPath;
    private FileWriter currentFile;
    private ClassDeclaration currentClass;
    private MethodDeclaration currentMethod;
    int numOfForeachs = 1;
    int numOfFors = 1;
    int numOfIfs = 1;
    int numOfCondExps = 1;
    String innerLoopStart;
    String updateLoop;
    String innerLoopEnd;
    String innerConditionalEnd;
    boolean getField = true;
    int tempAddSlot = 1;
    int numBranch = 0;
    public CodeGenerator(Graph<String> classHierarchy) {
        this.classHierarchy = classHierarchy;
        this.expressionTypeChecker = new ExpressionTypeChecker(classHierarchy);
        this.prepareOutputFolder();
    }

    private void prepareOutputFolder() {
        this.outputPath = "output/";
        String jasminPath = "utilities/jarFiles/jasmin.jar";
        String listClassPath = "utilities/codeGenerationUtilityClasses/List.j";
        String fptrClassPath = "utilities/codeGenerationUtilityClasses/Fptr.j";
        try{
            File directory = new File(this.outputPath);
            File[] files = directory.listFiles();
            if(files != null)
                for (File file : files)
                    file.delete();
            directory.mkdir();
        }
        catch(SecurityException e) { }
        copyFile(jasminPath, this.outputPath + "jasmin.jar");
        copyFile(listClassPath, this.outputPath + "List.j");
        copyFile(fptrClassPath, this.outputPath + "Fptr.j");
    }

    private void copyFile(String toBeCopied, String toBePasted) {
        try {
            File readingFile = new File(toBeCopied);
            File writingFile = new File(toBePasted);
            InputStream readingFileStream = new FileInputStream(readingFile);
            OutputStream writingFileStream = new FileOutputStream(writingFile);
            byte[] buffer = new byte[1024];
            int readLength;
            while ((readLength = readingFileStream.read(buffer)) > 0)
                writingFileStream.write(buffer, 0, readLength);
            readingFileStream.close();
            writingFileStream.close();
        } catch (IOException e) { }
    }

    private void createFile(String name) {
        try {
            String path = this.outputPath + name + ".j";
            File file = new File(path);
            file.createNewFile();
            FileWriter fileWriter = new FileWriter(path);
            this.currentFile = fileWriter;
        } catch (IOException e) {}
    }

    private void addCommand(String command) {
        try {
            command = String.join("\n\t\t", command.split("\n"));
            if(command.startsWith("Label_"))
                this.currentFile.write("\t" + command + "\n");
            else if(command.startsWith("."))
                this.currentFile.write(command + "\n");
            else
                this.currentFile.write("\t\t" + command + "\n");
            this.currentFile.flush();
        } catch (IOException e) {}
    }

    private String makeTypeSignatureCheckcast(Type t) {
        if(t instanceof IntType)
            return "java/lang/Integer";
        else if(t instanceof StringType)
            return "java/lang/String";
        else if(t instanceof BoolType)
            return "java/lang/Boolean";
        else if (t instanceof ListType)
            return "List";
        else if (t instanceof ClassType){
            String clsName = ((ClassType) t).getClassName().getName();
            return  clsName ;
        }
        else if (t instanceof FptrType)
            return "Fptr";
        return null;
    }

    private String makeTypeSignature(Type t) {
        if(t instanceof IntType)
            return "Ljava/lang/Integer;";
        else if(t instanceof StringType)
            return "Ljava/lang/String;";
        else if(t instanceof BoolType)
            return "Ljava/lang/Boolean;";
        else if (t instanceof ListType)
            return "LList;";
        else if (t instanceof ClassType){
            String clsName = ((ClassType) t).getClassName().getName();
            return "L" + clsName + ";";
        }
        else if (t instanceof FptrType)
            return "LFptr;";
        return null;
    }

    public void branch(Expression condition,String labelTrue,String labelFalse){
        numBranch++;

        if (condition.toString().split("_")[0].equals("Identifier")){
            addCommand(storeOrload(condition.toString(),"iload"));
            addCommand("ifeq " + labelFalse);
            addCommand("goto " + labelTrue);
            return;
        }
        if (condition.toString().split("_")[0].equals("BoolValue")){
            if(condition.toString().split("_")[1].equals("true"))
                addCommand("ldc 1");
            else addCommand("ldc 0");
            addCommand("ifeq " + labelFalse);
            addCommand("goto " + labelTrue);
            return;
        }
        BinaryExpression casted = (BinaryExpression) condition;
        BinaryOperator operator = casted.getBinaryOperator();
        String nNext = "Label_nNext" + numBranch;
        if (operator == BinaryOperator.and){
            branch(casted.getFirstOperand(),nNext ,labelFalse);
            addCommand(nNext  + ":");
            branch(casted.getSecondOperand(),labelTrue,labelFalse);
        }
        if (operator == BinaryOperator.or){
            branch(casted.getFirstOperand(),labelTrue ,nNext);
            addCommand(nNext  + ":");
            branch(casted.getSecondOperand(),labelTrue,labelFalse);
        }
    }


    private String initList(ListType listType){
        String instructions = "";

        instructions += "new List\n";
        instructions += "dup\n";

        instructions += "new java/util/ArrayList\n";
        instructions += "dup\n";
        instructions += "invokespecial java/util/ArrayList/<init>()V\n";
        for(int i=0; i< listType.getElementsTypes().size();i++){
            ListNameType lstNameType = listType.getElementsTypes().get(i);
            Type elementType = lstNameType.getType();
            instructions += "dup\n";
            if(elementType instanceof IntType){
                instructions +=("ldc 0\n");
                instructions +=("invokestatic java/lang/Integer/valueOf(I)Ljava/lang/Integer;\n");
                instructions += "invokevirtual java/util/ArrayList/add(Ljava/lang/Object;)Z\n";
                instructions += "pop\n";
            }
            else if(elementType instanceof BoolType){
                instructions +=("ldc 0\n");
                instructions +=("invokestatic java/lang/Boolean/valueOf(Z)Ljava/lang/Boolean;\n");
                instructions += "invokevirtual java/util/ArrayList/add(Ljava/lang/Object;)Z\n";
                instructions += "pop\n";
            }
            else if(elementType instanceof StringType){
                instructions +=("ldc \"\"\n");
                instructions += "invokevirtual java/util/ArrayList/add(Ljava/lang/Object;)Z\n";
                instructions += "pop\n";
            }
            else if(elementType instanceof ClassType || elementType instanceof FptrType){
                instructions += ("aconst_null\n");
                instructions += "invokevirtual java/util/ArrayList/add(Ljava/lang/Object;)Z\n";
                instructions += "pop\n";
            }
            else if(elementType instanceof ListType){
                instructions += initList((ListType) elementType);
                instructions += "invokevirtual java/util/ArrayList/add(Ljava/lang/Object;)Z\n";
                instructions += "pop\n";
            }
        }

        instructions += "invokespecial List/<init>(Ljava/util/ArrayList;)V\n";

        return instructions ;
    }

    private void addDefaultConstructor() {
        String instructions = "";
        instructions += ".method public <init>()V\n";
        instructions += ".limit stack 128\n";
        instructions += ".limit locals 128\n";

        instructions += "aload_0\n";
        if(currentClass.getParentClassName() != null)
            instructions += "invokespecial " + currentClass.getParentClassName().getName()+"/<init>()V\n";
        else
            instructions += "invokespecial java/lang/Object/<init>()V\n";

        for(FieldDeclaration FieldDec : currentClass.getFields()){
            VarDeclaration VarDec = FieldDec.getVarDeclaration();
            String VarName = VarDec.getVarName().getName();
            Type VarType = VarDec.getType();

            if(VarType instanceof IntType){
                instructions +=("aload_0\n");
                instructions +=("ldc 0\n");
                instructions +=("invokestatic java/lang/Integer/valueOf(I)Ljava/lang/Integer;\n");
                instructions +=("putfield " + currentClass.getClassName().getName() + "/" + VarName + " " + makeTypeSignature(VarType) + "\n");
            }
            else if(VarType instanceof BoolType){
                instructions +=("aload_0\n");
                instructions +=("ldc 0\n");
                instructions +=("invokestatic java/lang/Boolean/valueOf(Z)Ljava/lang/Boolean;\n");
                instructions +=("putfield " + currentClass.getClassName().getName() + "/" + VarName + " " + makeTypeSignature(VarType) + "\n");
            }
            else if(VarType instanceof StringType){
                instructions +=("aload_0\n");
                instructions +=("ldc \"\"\n");
                instructions +=("putfield " + currentClass.getClassName().getName() + "/" + VarName + " " + makeTypeSignature(VarType) + "\n");
            }
            else if(VarType instanceof ClassType || VarType instanceof FptrType){
                instructions += ("aload_0\n");
                instructions += ("aconst_null\n");
                instructions += ("putfield " + currentClass.getClassName().getName() + "/" + VarName + " " + makeTypeSignature(VarType) + "\n");
            }
            else if(VarType instanceof ListType){
                instructions += ("aload_0\n");
                instructions += initList((ListType) VarType);
                instructions +=("putfield " + currentClass.getClassName().getName() + "/" + VarName + " " + makeTypeSignature(VarType) + "\n");
            }
        }

        instructions += "return\n";
        addCommand(instructions);
        addCommand(".end method");

    }

    private void addStaticMainMethod() {
        addCommand(".method public static main([Ljava/lang/String;)V");
        addCommand(".limit stack 128");
        addCommand(".limit locals 128");
        addCommand("new Main");
        addCommand("invokespecial Main/<init>()V");
        addCommand("return");
        addCommand(".end method");
    }


    private int slotOf(String identifier) {
        if(identifier.equals("")){
            int x = tempAddSlot + currentMethod.getArgs().size() + currentMethod.getLocalVars().size();
            tempAddSlot++;
            return x;
        }
        for(int i=0;i<currentMethod.getArgs().size();i++){
            if(currentMethod.getArgs().get(i).getVarName().getName().equals(identifier)){
                return i + 1;
            }
        }
        for(int i =0 ;i<currentMethod.getLocalVars().size();i++){
            if(currentMethod.getLocalVars().get(i).getVarName().getName().equals(identifier))
                return i + 1 + currentMethod.getArgs().size();
        }

        return 0;
    }

    public String storeOrload(String value,String command){
        String result = "";
        int slot = slotOf(value);
        if (slot > 3)
            result += command + " " + slot;
        else
            result += command + "_" + slot;
        return result;
    }

    @Override
    public String visit(Program program) {

        for(ClassDeclaration cls: program.getClasses()){
            currentClass = cls;
            expressionTypeChecker.setCurrentClass(cls);
            cls.accept(this);
        }
        return null;
    }

    @Override
    public String visit(ClassDeclaration classDeclaration) {

        createFile(classDeclaration.getClassName().getName());
        addCommand(".class " + classDeclaration.getClassName().getName() + "\n");
        if(classDeclaration.getParentClassName() == null){
            String parent = "java/lang/Object";
            addCommand(".super " + parent + "\n\n");
        }
        else{
            addCommand(".super " + classDeclaration.getParentClassName().getName() + "\n\n");
        }
        for(FieldDeclaration field : classDeclaration.getFields()){
            field.accept(this);
        }
        if(classDeclaration.getConstructor() != null) {
            currentMethod = classDeclaration.getConstructor();
            expressionTypeChecker.setCurrentMethod(currentMethod);
            classDeclaration.getConstructor().accept(this);
        }
        else {
            addDefaultConstructor();
        }
        for(MethodDeclaration method : classDeclaration.getMethods()) {
            currentMethod = method;
            expressionTypeChecker.setCurrentMethod(method);
            method.accept(this);
        }

        return null;
    }

    @Override
    public String visit(ConstructorDeclaration constructorDeclaration) {

        if(constructorDeclaration.getArgs().size() > 0){
            addDefaultConstructor();
        }
        if(currentClass.getClassName().getName().equals("Main"))
            addStaticMainMethod();
        this.visit((MethodDeclaration) constructorDeclaration);
        return null;
    }

    @Override
    public String visit(MethodDeclaration methodDeclaration) {
        String args = "";
        String ReturnType = "";
        Type MethodRet = methodDeclaration.getReturnType();

        for (VarDeclaration vdec : methodDeclaration.getArgs()){
            args += makeTypeSignature(vdec.getType());
        }

        if(MethodRet instanceof NullType)
            ReturnType = "V";
        else ReturnType = makeTypeSignature(MethodRet);

        if(methodDeclaration instanceof ConstructorDeclaration) {
            addCommand(".method public <init>" + "(" + args +")"+ ReturnType);
            addCommand(".limit stack 128");
            addCommand(".limit locals 128");

            addCommand("aload_0\n");
            if(currentClass.getParentClassName() != null)
                addCommand("invokespecial " + currentClass.getParentClassName().getName()+"/<init>()V\n");
            else
                addCommand("invokespecial java/lang/Object/<init>()V\n");
            for(FieldDeclaration FieldDec : currentClass.getFields()){
                int slot = slotOf(FieldDec.getVarDeclaration().getVarName().getName());
                Type VarType = FieldDec.getVarDeclaration().getType();
                String VarName = FieldDec.getVarDeclaration().getVarName().getName();
                if(VarType instanceof IntType){
                    addCommand("aload_0");
                    addCommand("ldc 0");
                    addCommand("invokestatic java/lang/Integer/valueOf(I)Ljava/lang/Integer;");
                    addCommand("putfield " + currentClass.getClassName().getName() + "/" + VarName + " " + makeTypeSignature(VarType));
                }
                else if(VarType instanceof BoolType){
                    addCommand("aload_0");
                    addCommand("ldc 0");
                    addCommand("invokestatic java/lang/Boolean/valueOf(Z)Ljava/lang/Boolean;");
                    addCommand("putfield " + currentClass.getClassName().getName() + "/" + VarName + " " + makeTypeSignature(VarType));
                }
                else if(VarType instanceof StringType){
                    addCommand("aload_0");
                    addCommand("ldc \"\"");
                    addCommand("putfield " + currentClass.getClassName().getName() + "/" + VarName + " " + makeTypeSignature(VarType));
                }
                else if(VarType instanceof ClassType || VarType instanceof FptrType){
                    addCommand ("aload_0");
                    addCommand ("aconst_null");
                    addCommand ("putfield " + currentClass.getClassName().getName() + "/" + VarName + " " + makeTypeSignature(VarType));
                }
                else if(VarType instanceof ListType){
                    addCommand("aload_0");
                    addCommand(initList((ListType) VarType));
                    addCommand("putfield " + currentClass.getClassName().getName() + "/" + VarName + " " + makeTypeSignature(VarType));
                }
            }
        }
        else {
            addCommand(".method public " + methodDeclaration.getMethodName().getName() + "(" + args +")"+ ReturnType);
            addCommand(".limit stack 128");
            addCommand(".limit locals 128");
        }

        for (VarDeclaration varDec : methodDeclaration.getLocalVars())
            varDec.accept(this);
        for (Statement stmt : methodDeclaration.getBody())
            stmt.accept(this);
        if (!methodDeclaration.getDoesReturn() ) {
            addCommand("return");
        }
        addCommand(".end method\n");
        return null;
    }

    @Override
    public String visit(FieldDeclaration fieldDeclaration) {
        String VarType = "";
        Type FieldDecType = fieldDeclaration.getVarDeclaration().getType();
        VarType = makeTypeSignature(FieldDecType);
        addCommand(".field " + fieldDeclaration.getVarDeclaration().getVarName().getName() + " " +VarType );
        return null;
    }

    @Override
    public String visit(VarDeclaration varDeclaration) {
        int slot = slotOf(varDeclaration.getVarName().getName());
        Type varType = varDeclaration.getType();
        if (varType instanceof IntType){
            addCommand("ldc 0");
            addCommand("invokestatic java/lang/Integer/valueOf(I)Ljava/lang/Integer;");
            addCommand(storeOrLoadWithoutSlot("astore",slot));
        }
        if(varType instanceof BoolType){
            addCommand("ldc 0");
            addCommand("invokestatic java/lang/Boolean/valueOf(Z)Ljava/lang/Boolean;");
            addCommand(storeOrLoadWithoutSlot("astore",slot));
        }
        else if (varType instanceof StringType){
            addCommand("ldc \"\"");
            addCommand(storeOrLoadWithoutSlot("astore",slot));
        }
        else if(varType instanceof ClassType || varType instanceof FptrType){
            addCommand ("aconst_null");
            addCommand (storeOrLoadWithoutSlot("astore",slot));
        }
        else if(varType instanceof ListType){
            addCommand(initList((ListType) varType));
            addCommand (storeOrLoadWithoutSlot("astore",slot));
        }

        return null;
    }

    @Override
    public String visit(AssignmentStmt assignmentStmt) {
        BinaryExpression AssignInBinary = new BinaryExpression(assignmentStmt.getlValue(),assignmentStmt.getrValue(),BinaryOperator.assign);
        addCommand(AssignInBinary.accept(this));
        addCommand("pop");
        return null;
    }

    @Override
    public String visit(BlockStmt blockStmt) {
        String prevInnerLoopStart = innerLoopStart;
        String prevUpdateLoop = updateLoop;
        String prevInnerLoopEnd = innerLoopEnd;
        String prevInnerCondEnd = innerConditionalEnd;
        for (Statement stmt:blockStmt.getStatements())
            stmt.accept(this);
        innerLoopStart = prevInnerLoopStart;
        updateLoop = prevUpdateLoop;
        innerLoopEnd = prevInnerLoopEnd;
        innerConditionalEnd = prevInnerCondEnd;
        return null;
    }

    @Override
    public String visit(ConditionalStmt conditionalStmt) {
        String prevInnerCondEnd = innerConditionalEnd;
        String commands = "";
        int n = numOfIfs;
        numOfIfs++;
        innerConditionalEnd = "Label_exitIf" + n;
        addCommand("Label_startIf" + n + ":");
        addCommand(conditionalStmt.getCondition().accept(this));
        if (conditionalStmt.getElseBody() != null) {
            addCommand("ifeq Label_" + conditionalStmt.getElseBody().getLine());
            conditionalStmt.getThenBody().accept(this);
            addCommand("goto " + innerConditionalEnd);
            addCommand("Label_" + conditionalStmt.getElseBody().getLine() + ":");
            conditionalStmt.getElseBody().accept(this);
        }
        else {
            addCommand("ifeq " + innerConditionalEnd);
            conditionalStmt.getThenBody().accept(this);
        }
        addCommand(innerConditionalEnd + ":");
        innerConditionalEnd = prevInnerCondEnd;
        return null;
    }

    @Override
    public String visit(MethodCallStmt methodCallStmt) {
        expressionTypeChecker.setIsInMethodCallStmt(true);
        addCommand(methodCallStmt.getMethodCall().accept(this));
        addCommand("pop");
        expressionTypeChecker.setIsInMethodCallStmt(false);
        return null;
    }

    @Override
    public String visit(PrintStmt print) {
        addCommand("getstatic java/lang/System/out Ljava/io/PrintStream;");
        addCommand(print.getArg().accept(this));
        Type ArgType = print.getArg().accept(expressionTypeChecker);
        String arg;
        if(ArgType instanceof BoolType)
            arg = "Z";
        else if(ArgType instanceof IntType)
            arg = "I";
        else
            arg = "Ljava/lang/String;";
        addCommand("invokevirtual java/io/PrintStream/print("+arg+")"+"V");
        return null;
    }

    @Override
    public String visit(ReturnStmt returnStmt) {
        Type type = returnStmt.getReturnedExpr().accept(expressionTypeChecker);
        if(type instanceof NullType) {
            addCommand("return");
        }
        else {
            addCommand(returnStmt.getReturnedExpr().accept(this));
            if(type instanceof BoolType)
                addCommand("invokestatic java/lang/Boolean/valueOf(Z)Ljava/lang/Boolean;\n");
            if(type instanceof IntType)
                addCommand("invokestatic java/lang/Integer/valueOf(I)Ljava/lang/Integer;\n");
            addCommand("areturn");
        }
        return null;
    }

    @Override
    public String visit(BreakStmt breakStmt) {
        addCommand("goto " + innerLoopEnd );
        return null;
    }

    @Override
    public String visit(ContinueStmt continueStmt) {
        addCommand("goto " + updateLoop);
        return null;
    }

    @Override
    public String visit(ForeachStmt foreachStmt) {
        innerLoopStart = "Label_startForeach" + numOfForeachs;
        updateLoop = "Label_updateForeach" + numOfForeachs;
        innerLoopEnd = "Label_exitForeach" + numOfForeachs;

        int TempSlot = slotOf("");
        int n = numOfForeachs;
        int listSize = ((ListType)foreachStmt.getList().accept(expressionTypeChecker)).getElementsTypes().size();
        numOfForeachs++;

        addCommand("ldc 0");
        addCommand(storeOrLoadWithoutSlot("istore",TempSlot));

        addCommand("Label_startForeach" + n + ":");

        addCommand(storeOrLoadWithoutSlot("iload",TempSlot));
        addCommand("ldc " + listSize);
        addCommand("if_icmpge Label_exitForeach" + n);

        String beforeAssign = "";
        beforeAssign += foreachStmt.getList().accept(this) + "\n";


        beforeAssign += (storeOrLoadWithoutSlot("iload",TempSlot)) + "\n";
        beforeAssign += ("invokevirtual List/getElement(I)Ljava/lang/Object;") + "\n";
        Type VarType = foreachStmt.getVariable().accept(expressionTypeChecker);
        beforeAssign +=("checkcast " + makeTypeSignatureCheckcast(VarType));
        addCommand(beforeAssign);

        int slot = slotOf(foreachStmt.getVariable().getName());
        addCommand(storeOrLoadWithoutSlot("astore",slot));

        foreachStmt.getBody().accept(this);
        addCommand("Label_updateForeach" + n + ":");
        addCommand("iinc " + TempSlot + " 1");
        addCommand("goto Label_startForeach" + n);
        tempAddSlot--;
        addCommand("Label_exitForeach" + n + ":");
        return null;
    }

    @Override
    public String visit(ForStmt forStmt) {
        innerLoopStart = "Label_startFor" + numOfFors;
        updateLoop = "Label_updateFor" + numOfFors;
        innerLoopEnd = "Label_endFor" + numOfFors;
        innerConditionalEnd = innerLoopEnd;
        int n = numOfFors;
        forStmt.getInitialize().accept(this);
        addCommand("Label_startFor" + n + ":");
        numOfFors++;
        addCommand(forStmt.getCondition().accept(this));
        addCommand("ifeq Label_endFor" + n);

        forStmt.getBody().accept(this);
        addCommand("Label_updateFor" + n + ":");
        forStmt.getUpdate().accept(this);
        addCommand("goto Label_startFor" + n);
        addCommand("Label_endFor" + n + ":");
        return null;
    }

    @Override
    public String visit(BinaryExpression binaryExpression) {
        BinaryOperator operator = binaryExpression.getBinaryOperator();
        Type leftType = binaryExpression.getFirstOperand().accept(expressionTypeChecker);
        Type rightType = binaryExpression.getSecondOperand().accept(expressionTypeChecker);
        String commands = "";

        if(operator != BinaryOperator.assign) {
            getField = true;
            commands += binaryExpression.getFirstOperand().accept(this);
            commands += binaryExpression.getSecondOperand().accept(this);
        }

        if (operator == BinaryOperator.add) {
            commands += "iadd\n";
        }
        else if (operator == BinaryOperator.sub) {
            commands += "isub\n";
        }
        else if (operator == BinaryOperator.mult) {
            commands += "imul\n";
        }
        else if (operator == BinaryOperator.div) {
            commands += "idiv\n";
        }
        else if (operator == BinaryOperator.mod) {
            commands += "irem\n";
        }
        else if(operator == BinaryOperator.gt) {
            commands += "if_icmple " + "Label_pushZero" + numOfCondExps + "\n";
            commands += "ldc 1\n";
            commands += "goto " + "Label_pushZeroEnd" +numOfCondExps + "\n";
            commands += "Label_pushZero" +numOfCondExps + ":\n";
            commands += "ldc 0\n";
            commands += "Label_pushZeroEnd" + numOfCondExps + ":\n";
            numOfCondExps++;
        }
        else if (operator == BinaryOperator.lt) {
            commands += "if_icmpge " + "Label_pushZero" + numOfCondExps + "\n";
            commands += "ldc 1\n";
            commands += "goto " + "Label_pushZeroEnd" +numOfCondExps + "\n";
            commands += "Label_pushZero" +numOfCondExps + ":\n";
            commands += "ldc 0\n";
            commands += "Label_pushZeroEnd" + numOfCondExps + ":\n";
            numOfCondExps++;
        }
        else if (operator == BinaryOperator.eq) {
            if (leftType instanceof StringType || leftType instanceof FptrType || leftType instanceof ClassType || leftType instanceof NullType)
                commands += "if_acmpeq " + "Label_pushOne" + numOfCondExps + "\n";
            else
                commands += "if_icmpeq " + "Label_pushOne" + numOfCondExps + "\n";
            commands += "ldc 0\n";
            commands += "goto " + "Label_pushOneEnd" +numOfCondExps + "\n";
            commands += "Label_pushOne" +numOfCondExps + ":\n";
            commands += "ldc 1\n";
            commands += "Label_pushOneEnd" + numOfCondExps + ":\n";
            numOfCondExps++;
        }
        else if (operator == BinaryOperator.neq) {
            if (leftType instanceof StringType || leftType instanceof FptrType || leftType instanceof ClassType || leftType instanceof NullType)
                commands += "if_acmpeq " + "Label_pushZero" + numOfCondExps + "\n";
            else
                commands += "if_icmpeq " + "Label_pushZero" + numOfCondExps + "\n";
            commands += "ldc 1\n";
            commands += "goto " + "Label_pushZeroEnd" + numOfCondExps + "\n";
            commands += "Label_pushZero" +numOfCondExps + ":\n";
            commands += "ldc 0\n";
            commands += "Label_pushZeroEnd" + numOfCondExps + ":\n";
            numOfCondExps++;
        }
        else if(operator == BinaryOperator.and) {
            branch(binaryExpression,"Label_pushOne" + numOfCondExps,"Label_pushZero" + numOfCondExps);
            commands += "Label_pushZero" + numOfCondExps + ":\n";
            commands += "ldc 0\n";
            commands += "goto Label_pushOneEnd" + numOfCondExps + "\n";
            commands += "Label_pushOne" + numOfCondExps + ":\n";
            commands += "ldc 1\n";
            commands += "Label_pushOneEnd" + numOfCondExps + ":\n";
            numOfCondExps++;
        }
        else if(operator == BinaryOperator.or) {
            branch(binaryExpression,"Label_pushOne" + numOfCondExps,"Label_pushZero" + numOfCondExps);
            commands += "Label_pushZero" + numOfCondExps + ":\n";
            commands += "ldc 0\n";
            commands += "goto Label_pushOneEnd" + numOfCondExps + "\n";
            commands += "Label_pushOne" + numOfCondExps + ":\n";
            commands += "ldc 1\n";
            commands += "Label_pushOneEnd" + numOfCondExps + ":\n";
            numOfCondExps++;
        }
        else if(operator == BinaryOperator.assign) {
            Type firstType = binaryExpression.getFirstOperand().accept(expressionTypeChecker);
            String secondOperandCommands = binaryExpression.getSecondOperand().accept(this);
            Type secondType = binaryExpression.getSecondOperand().accept(expressionTypeChecker);

            if(firstType instanceof ListType) {
                String tmp = "new List\n";
                tmp += "dup\n";
                tmp += secondOperandCommands;
                secondOperandCommands = tmp;
                secondOperandCommands += "invokespecial List/<init>(LList;)V\n";
            }
            if(secondType instanceof BoolType)
                secondOperandCommands += "invokestatic java/lang/Boolean/valueOf(Z)Ljava/lang/Boolean;\n";
            if(secondType instanceof IntType)
                secondOperandCommands += "invokestatic java/lang/Integer/valueOf(I)Ljava/lang/Integer;\n";

            if(binaryExpression.getFirstOperand() instanceof Identifier) {
                int slot = slotOf(((Identifier)binaryExpression.getFirstOperand()).getName());
                commands += secondOperandCommands;
                commands += "dup\n";
                commands += storeOrLoadWithoutSlot("astore",slot);
            }

            else if(binaryExpression.getFirstOperand() instanceof ListAccessByIndex) {
                int tempSlot = slotOf("");
                commands += ((ListAccessByIndex)binaryExpression.getFirstOperand()).getInstance().accept(this);
                commands += ((ListAccessByIndex)binaryExpression.getFirstOperand()).getIndex().accept(this);
                commands += secondOperandCommands;
                commands += "dup\n";
                commands += storeOrLoadWithoutSlot("astore",tempSlot);
                commands += "invokevirtual List/setElement(ILjava/lang/Object;)V\n";
                commands += storeOrLoadWithoutSlot("aload",tempSlot);
            }

            else if(binaryExpression.getFirstOperand() instanceof ObjectOrListMemberAccess) {
                Expression instance = ((ObjectOrListMemberAccess) binaryExpression.getFirstOperand()).getInstance();
                Type memberType = binaryExpression.getFirstOperand().accept(expressionTypeChecker);
                String memberName = ((ObjectOrListMemberAccess) binaryExpression.getFirstOperand()).getMemberName().getName();
                Type instanceType = instance.accept(expressionTypeChecker);
                if(instanceType instanceof ListType) {
                    int IndexOfObject = 0;
                    ListType listType = (ListType)instanceType;
                    for(ListNameType  listNameType: listType.getElementsTypes()){
                        if(listNameType.getName() == null){
                            IndexOfObject++;
                            continue;
                        }
                        if(listNameType.getName().getName().equals(memberName))
                            break;
                        IndexOfObject++;
                    }
                    int tempSlot = slotOf("");
                    commands += ((ObjectOrListMemberAccess) binaryExpression.getFirstOperand()).getInstance().accept(this);
                    commands += "ldc " + IndexOfObject + "\n";
                    commands += secondOperandCommands;
                    commands += "dup\n";
                    commands += storeOrLoadWithoutSlot("astore",tempSlot);
                    commands += "invokevirtual List/setElement(ILjava/lang/Object;)V\n";
                    commands += storeOrLoadWithoutSlot("aload",tempSlot);

                }
                else if(instanceType instanceof ClassType) {
                    int tempSlot = slotOf("");
                    commands += ((ObjectOrListMemberAccess)binaryExpression.getFirstOperand()).getInstance().accept(this);
                    commands += secondOperandCommands;
                    commands += "dup\n";
                    commands += storeOrLoadWithoutSlot("astore",tempSlot);
                    getField = false;
                    commands += ((ObjectOrListMemberAccess) binaryExpression.getFirstOperand()).accept(this);
                    getField = true;
                    commands += storeOrLoadWithoutSlot("aload",tempSlot);
                }
            }
        }
        return commands;
    }

    @Override
    public String visit(UnaryExpression unaryExpression) {
        UnaryOperator operator = unaryExpression.getOperator();
        String commands = "";
        if(operator == UnaryOperator.minus) {
            commands += unaryExpression.getOperand().accept(this);
            commands += "ldc -1\n";
            commands += "imul\n";
        }
        else if(operator == UnaryOperator.not) {
            commands += unaryExpression.getOperand().accept(this);
            commands += "ldc -1\n";
            commands += "imul\n";
            commands += "ldc 1\n";
            commands += "iadd\n";
        }
        else if((operator == UnaryOperator.predec) || (operator == UnaryOperator.preinc)) {
            if(unaryExpression.getOperand() instanceof Identifier) {
                int slot = slotOf(((Identifier) unaryExpression.getOperand()).getName());
                commands += unaryExpression.getOperand().accept(this);

                commands += "ldc 1\n";
                if(operator == UnaryOperator.predec)
                    commands += "isub\n";
                else
                    commands += "iadd\n";

                commands += "invokestatic java/lang/Integer/valueOf(I)Ljava/lang/Integer;\n";
                commands += storeOrLoadWithoutSlot("astore",slot);
                commands += storeOrLoadWithoutSlot("aload",slot);
                commands += "invokevirtual java/lang/Integer/intValue()I\n";
            }

            else if(unaryExpression.getOperand() instanceof ListAccessByIndex) {
                commands += ((ListAccessByIndex)unaryExpression.getOperand()).getInstance().accept(this);
                commands += ((ListAccessByIndex)unaryExpression.getOperand()).getIndex().accept(this);
                commands += "dup2\n";
                commands += unaryExpression.getOperand().accept(this);
                commands += "ldc 1\n";
                if(operator == UnaryOperator.predec)
                    commands += "isub\n";
                else
                    commands += "iadd\n";

                commands += "invokestatic java/lang/Integer/valueOf(I)Ljava/lang/Integer;\n";
                commands += "invokevirtual List/setElement(ILjava/lang/Object;)V\n";

                commands += "invokevirtual List/getElement(I)Ljava/lang/Object;\n";
                commands += "checkcast java/lang/Integer\n";
                commands += "invokevirtual java/lang/Integer/intValue()I\n";

            }
            else if(unaryExpression.getOperand() instanceof ObjectOrListMemberAccess) {
                Expression instance = ((ObjectOrListMemberAccess) unaryExpression.getOperand()).getInstance();
                Type memberType = unaryExpression.getOperand().accept(expressionTypeChecker);
                String memberName = ((ObjectOrListMemberAccess) unaryExpression.getOperand()).getMemberName().getName();
                Type instanceType = instance.accept(expressionTypeChecker);
                if(instanceType instanceof ListType) {
                    int index = 0;
                    ListType listType = (ListType)instanceType;
                    for(ListNameType  listNameType: listType.getElementsTypes()){
                        if(listNameType.getName() == null){
                            index++;
                            continue;
                        }
                        if(listNameType.getName().getName().equals(memberName))
                            break;
                        index++;
                    }
                    commands += ((ObjectOrListMemberAccess) unaryExpression.getOperand()).getInstance().accept(this);
                    commands += "ldc " + index + "\n";
                    commands += "dup2\n";
                    commands+=unaryExpression.getOperand().accept(this);

                    commands += "ldc 1\n";
                    if(operator == UnaryOperator.predec)
                        commands += "isub\n";
                    else
                        commands += "iadd\n";

                    commands += "invokestatic java/lang/Integer/valueOf(I)Ljava/lang/Integer;\n";
                    commands += "invokevirtual List/setElement(ILjava/lang/Object;)V\n";

                    commands += "invokevirtual List/getElement(I)Ljava/lang/Object;\n";
                    commands += "checkcast java/lang/Integer\n";
                    commands += "invokevirtual java/lang/Integer/intValue()I\n";
                }
                else if(instanceType instanceof ClassType) {
                    commands += ((ObjectOrListMemberAccess) unaryExpression.getOperand()).getInstance().accept(this);
                    commands += ((ObjectOrListMemberAccess) unaryExpression.getOperand()).accept(this);

                    commands += "ldc 1\n";
                    if(operator == UnaryOperator.predec)
                        commands += "isub\n";
                    else
                        commands += "iadd\n";

                    commands += "invokestatic java/lang/Integer/valueOf(I)Ljava/lang/Integer;\n";
                    getField = false;
                    commands += ((ObjectOrListMemberAccess) unaryExpression.getOperand()).accept(this);
                    getField = true;
                    commands += ((ObjectOrListMemberAccess) unaryExpression.getOperand()).accept(this);

                }
            }
        }
        else if((operator == UnaryOperator.postdec) || (operator == UnaryOperator.postinc)) {
            if(unaryExpression.getOperand() instanceof Identifier) {
                int slot = slotOf(((Identifier) unaryExpression.getOperand()).getName());
                commands += storeOrLoadWithoutSlot("aload",slot);
                commands += "invokevirtual java/lang/Integer/intValue()I\n";

                commands += unaryExpression.getOperand().accept(this);
                commands += "ldc 1\n";
                if(operator == UnaryOperator.postdec)
                    commands += "isub\n";
                else
                    commands += "iadd\n";

                commands += "invokestatic java/lang/Integer/valueOf(I)Ljava/lang/Integer;\n";
                commands += storeOrLoadWithoutSlot("astore",slot);

            }
            else if(unaryExpression.getOperand() instanceof ListAccessByIndex) {

                commands += ((ListAccessByIndex)unaryExpression.getOperand()).getInstance().accept(this);
                commands += ((ListAccessByIndex)unaryExpression.getOperand()).getIndex().accept(this);
                commands += "invokevirtual List/getElement(I)Ljava/lang/Object;\n";
                commands += "checkcast java/lang/Integer\n";
                commands += "invokevirtual java/lang/Integer/intValue()I\n";

                commands += ((ListAccessByIndex)unaryExpression.getOperand()).getInstance().accept(this);
                commands += ((ListAccessByIndex)unaryExpression.getOperand()).getIndex().accept(this);

                commands += unaryExpression.getOperand().accept(this);
                commands += "ldc 1\n";
                if(operator == UnaryOperator.postdec)
                    commands += "isub\n";
                else
                    commands += "iadd\n";

                commands += "invokestatic java/lang/Integer/valueOf(I)Ljava/lang/Integer;\n";
                commands += "invokevirtual List/setElement(ILjava/lang/Object;)V\n";

            }
            else if(unaryExpression.getOperand() instanceof ObjectOrListMemberAccess) {
                Expression instance = ((ObjectOrListMemberAccess) unaryExpression.getOperand()).getInstance();
                Type memberType = unaryExpression.getOperand().accept(expressionTypeChecker);
                String memberName = ((ObjectOrListMemberAccess) unaryExpression.getOperand()).getMemberName().getName();
                Type instanceType = instance.accept(expressionTypeChecker);
                if(instanceType instanceof ListType) {
                    int index = 0;
                    ListType listType = (ListType)instanceType;
                    for(ListNameType  listNameType: listType.getElementsTypes()){
                        if(listNameType.getName() == null){
                            index++;
                            continue;
                        }
                        if(listNameType.getName().getName().equals(memberName))
                            break;
                        index++;
                    }

                    commands += ((ObjectOrListMemberAccess) unaryExpression.getOperand()).getInstance().accept(this);
                    commands += "ldc " + index + "\n";
                    commands += "invokevirtual List/getElement(I)Ljava/lang/Object;\n";
                    commands += "checkcast java/lang/Integer\n";
                    commands += "invokevirtual java/lang/Integer/intValue()I\n";

                    commands += ((ObjectOrListMemberAccess) unaryExpression.getOperand()).getInstance().accept(this);
                    commands += "ldc " + index + "\n";
                    commands+=unaryExpression.getOperand().accept(this);

                    commands += "ldc 1\n";
                    if(operator == UnaryOperator.postdec)
                        commands += "isub\n";
                    else
                        commands += "iadd\n";

                    commands += "invokestatic java/lang/Integer/valueOf(I)Ljava/lang/Integer;\n";
                    commands += "invokevirtual List/setElement(ILjava/lang/Object;)V\n";

                }
                else if(instanceType instanceof ClassType) {
                    commands += ((ObjectOrListMemberAccess) unaryExpression.getOperand()).accept(this);

                    commands += ((ObjectOrListMemberAccess) unaryExpression.getOperand()).getInstance().accept(this);

                    commands += ((ObjectOrListMemberAccess) unaryExpression.getOperand()).accept(this);

                    commands += "ldc 1\n";
                    if(operator == UnaryOperator.postdec)
                        commands += "isub\n";
                    else
                        commands += "iadd\n";

                    commands += "invokestatic java/lang/Integer/valueOf(I)Ljava/lang/Integer;\n";
                    getField = false;
                    commands += ((ObjectOrListMemberAccess) unaryExpression.getOperand()).accept(this);
                    getField = true;
                }
            }
        }
        return commands;
    }

    @Override
    public String visit(ObjectOrListMemberAccess objectOrListMemberAccess) {

        Type memberType = objectOrListMemberAccess.accept(expressionTypeChecker);
        Type instanceType = objectOrListMemberAccess.getInstance().accept(expressionTypeChecker);
        String memberName = objectOrListMemberAccess.getMemberName().getName();
        String commands = "";
        if(instanceType instanceof ClassType) {
            String className = ((ClassType) instanceType).getClassName().getName();
            try {
                SymbolTable classSymbolTable = ((ClassSymbolTableItem) SymbolTable.root.getItem(ClassSymbolTableItem.START_KEY + className, true)).getClassSymbolTable();
                try {
                    classSymbolTable.getItem(FieldSymbolTableItem.START_KEY + memberName, true);
                    if (getField) {
                        commands += objectOrListMemberAccess.getInstance().accept(this);
                        commands += "getfield " + className + "/" + memberName + " " + makeTypeSignature(memberType) + "\n";
                        if (memberType instanceof BoolType)
                            commands += "invokevirtual java/lang/Boolean/booleanValue()Z\n";
                        if (memberType instanceof IntType)
                            commands += "invokevirtual java/lang/Integer/intValue()I\n";
                    }
                    else
                        commands += "putfield " + className + "/" + memberName + " " + makeTypeSignature(memberType) + "\n";

                } catch (ItemNotFoundException memberIsMethod) {
                    commands += "new Fptr\n";
                    commands += "dup\n";
                    commands += objectOrListMemberAccess.getInstance().accept(this);
                    commands += "ldc \"" + memberName + "\"\n";
                    commands += "invokespecial Fptr/<init>(Ljava/lang/Object;Ljava/lang/String;)V\n";
                }
            } catch (ItemNotFoundException classNotFound) {}
        }

        else if(instanceType instanceof ListType) {

            int index = 0;
            ListType listType = (ListType)instanceType;
            for(ListNameType  listNameType: listType.getElementsTypes()){
                if(listNameType.getName() == null){
                    index++;
                    continue;
                }
                if(listNameType.getName().getName().equals(memberName))
                    break;
                index++;
            }

            commands += objectOrListMemberAccess.getInstance().accept(this);
            commands += "ldc " + index + "\n";
            commands += "invokevirtual List/getElement(I)Ljava/lang/Object;\n";

            commands += "checkcast " + makeTypeSignatureCheckcast(memberType) + "\n";

            if (memberType instanceof BoolType)
                commands += "invokevirtual java/lang/Boolean/booleanValue()Z\n";
            if (memberType instanceof IntType)
                commands += "invokevirtual java/lang/Integer/intValue()I\n";
        }
        return commands;
    }

    @Override
    public String visit(Identifier identifier) {
        String commands = "";
        int slot = slotOf(identifier.getName());
        commands += storeOrLoadWithoutSlot("aload",slot);
        Type IdType = identifier.accept(expressionTypeChecker);
        commands += "checkcast " + makeTypeSignatureCheckcast(IdType) + "\n";
        if (IdType instanceof BoolType)
            commands += "invokevirtual java/lang/Boolean/booleanValue()Z\n";

        if (IdType instanceof IntType)
            commands += "invokevirtual java/lang/Integer/intValue()I\n";
        return commands;
    }

    @Override
    public String visit(ListAccessByIndex listAccessByIndex) {

        String commands = "";
        Type listAccType = listAccessByIndex.accept(expressionTypeChecker);
        commands += listAccessByIndex.getInstance().accept(this);
        commands += listAccessByIndex.getIndex().accept(this);

        commands += "invokevirtual List/getElement(I)Ljava/lang/Object;\n";

        commands += "checkcast " + makeTypeSignatureCheckcast(listAccType) + "\n";

        if(listAccType instanceof BoolType)
            commands += "invokevirtual java/lang/Integer/booleanValue()Z\n";
        if(listAccType instanceof IntType)
            commands += "invokevirtual java/lang/Integer/intValue()I\n";

        return commands;
    }


    public String storeOrLoadWithoutSlot(String Command,int slot){
        if (slot > 3)
            return (Command +" "+ slot + "\n" ) ;
        else
            return ( Command + "_" + slot + "\n");
    }

    @Override
    public String visit(MethodCall methodCall) {
        String commands = "";
        int TempVar = slotOf("");
        ArrayList<Expression> args = methodCall.getArgs();
        Type retType = ((FptrType) methodCall.getInstance().accept(this.expressionTypeChecker)).getReturnType();
        commands += methodCall.getInstance().accept(this);
        commands += "new java/util/ArrayList\n";
        commands += "dup\n";
        commands += "invokespecial java/util/ArrayList/<init>()V\n";
        commands += storeOrLoadWithoutSlot("astore",TempVar);

        for(Expression arg : methodCall.getArgs()){
            commands += storeOrLoadWithoutSlot("aload",TempVar);

            Type argType = arg.accept(expressionTypeChecker);

            if(argType instanceof ListType) {
                commands += "new List\n";
                commands += "dup\n";
            }
            commands += arg.accept(this);

            if(argType instanceof BoolType)
                commands += "invokestatic java/lang/Boolean/valueOf(Z)Ljava/lang/Boolean;\n";
            if(argType instanceof IntType)
                commands += "invokestatic java/lang/Integer/valueOf(I)Ljava/lang/Integer;\n";
            if(argType instanceof ListType) {
                commands += "invokespecial List/<init>(LList;)V\n";
            }

            commands += "invokevirtual java/util/ArrayList/add(Ljava/lang/Object;)Z\n";
            commands += "pop\n";
        }
        commands += storeOrLoadWithoutSlot("aload",TempVar);
        commands += "invokevirtual Fptr/invoke(Ljava/util/ArrayList;)Ljava/lang/Object;\n";

        commands += "checkcast " + makeTypeSignatureCheckcast(retType) + "\n";

        if (retType instanceof BoolType)
            commands += "invokevirtual java/lang/Boolean/booleanValue()Z\n";
        if (retType instanceof IntType)
            commands += "invokevirtual java/lang/Integer/intValue()I\n";
        return commands;
    }


    @Override
    public String visit(NewClassInstance newClassInstance) {
        String commands = "";
        String args = "";
        String className = newClassInstance.getClassType().getClassName().getName();
        commands += "new " + newClassInstance.getClassType().getClassName().getName() + "\n";
        commands += "dup\n";

        for (Expression exp : newClassInstance.getArgs()) {
            commands += exp.accept(this);
            Type expType = exp.accept(expressionTypeChecker);
            args += makeTypeSignature(expType) ;
            if (expType instanceof BoolType)
                commands += "invokestatic java/lang/Boolean/valueOf(Z)Ljava/lang/Boolean;\n";
            if (expType instanceof IntType)
                commands += "invokestatic java/lang/Integer/valueOf(I)Ljava/lang/Integer;\n";
        }

        commands += "invokespecial " + className + "/<init>(" + args + ")V\n";

        return commands;
    }

    @Override
    public String visit(ThisClass thisClass) {
        String commands = "";
        commands += ("aload_0\n");
        return commands;
    }

    @Override
    public String visit(ListValue listValue) {
        String commands = "";
        int CurrIndex = slotOf("");
        commands += "new List\n";
        commands += "dup\n";
        commands += "new java/util/ArrayList\n";
        commands += "dup\n";
        commands += "invokespecial java/util/ArrayList/<init>()V\n";
        commands += storeOrLoadWithoutSlot("astore",CurrIndex);

        for (Expression element: listValue.getElements()) {
            commands += storeOrLoadWithoutSlot("aload",CurrIndex);
            commands += element.accept(this);
            Type elementType = element.accept(expressionTypeChecker);

            if(elementType instanceof BoolType)
                commands += "invokestatic java/lang/Boolean/valueOf(Z)Ljava/lang/Boolean;\n";
            if(elementType instanceof IntType)
                commands += "invokestatic java/lang/Integer/valueOf(I)Ljava/lang/Integer;\n";

            commands += "invokevirtual java/util/ArrayList/add(Ljava/lang/Object;)Z\n";
            commands += "pop\n";
        }
        commands += storeOrLoadWithoutSlot("aload",CurrIndex);
        commands += "invokespecial List/<init>(Ljava/util/ArrayList;)V\n";
        return commands;
    }

    @Override
    public String visit(NullValue nullValue) {
        String commands = "";
        commands += "aconst_null\n";
        return commands;
    }

    @Override
    public String visit(IntValue intValue) {
        String commands = "";
        commands += "ldc " + intValue.getConstant() + "\n";
        return commands;
    }

    @Override
    public String visit(BoolValue boolValue) {
        String commands = "";
        if(boolValue.getConstant())
            commands += "ldc 1\n";
        else
            commands += "ldc 0\n";
        return commands;
    }

    @Override
    public String visit(StringValue stringValue) {
        String commands = "";
        commands += "ldc \"" + stringValue.getConstant() + "\"\n";
        return commands;
    }
}