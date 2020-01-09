#include "header.h"
#include "myRegister.h"
#include "offsetInAR.h"
#include "printSourceFile.h"
#include "symbolTable.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>


#define node_type(node) node->nodeType
#define data_type(node) node->dataType
#define id_sym(node) node->semantic_value.identifierSemanticValue.symbolTableEntry
#define id_name(node) node->semantic_value.identifierSemanticValue.identifierName
#define id_kind(node) node->semantic_value.identifierSemanticValue.kind
#define decl_kind(node) node->semantic_value.declSemanticValue.kind
#define stmt_kind(node) node->semantic_value.stmtSemanticValue.kind
#define expr_kind(node) node->semantic_value.exprSemanticValue.kind
#define sym_typedesc(sym) sym->attribute->attr.typeDescriptor
#define const_ival(node) node->semantic_value.const1->const_u.intval
#define const_fval(node) node->semantic_value.const1->const_u.fval
#define const_sval(node) node->semantic_value.const1->const_u.sc
#define expr_const_eval(node) node->semantic_value.exprSemanticValue.isConstEval
#define const_type(node) node->semantic_value.const1->const_type
#define expr_bin_op(node) node->semantic_value.exprSemanticValue.op.binaryOp
#define expr_uni_op(node) node->semantic_value.exprSemanticValue.op.unaryOp
#define expr_eval(node) node->semantic_value.exprSemanticValue.constEvalValue


FILE *g_codeGenOutputFp = NULL;
char *g_currentFunctionName = NULL;

int getLabelNumber();
int codeGenConstantLabel(C_type constantType, void *valuePtr);
void codeGenGetBoolOfFloat(int boolRegIndex, int floatRegIndex);
void codeGenPrepareRegister(ProcessorType processorType, int regIndex,
                            int needToBeLoaded, int workRegIndexIfPseudo,
                            char **regName);
void codeGenSaveToMemoryIfPsuedoRegister(ProcessorType processorType,
                                         int regIndex, char *regName);
void codeGenLogicalInstruction(ProcessorType processorType, char *instruction,
                               int dstRegIndex, int srcReg1Index,
                               int srcReg2Index);
// reg1 is dst
void codeGen2RegInstruction(ProcessorType processorType, char *instruction,
                            int reg1Index, int reg2Index);
// reg1 is dst
void codeGen3RegInstruction(ProcessorType processorType, char *instruction,
                            int reg1Index, int reg2Index, int reg3Index);
void codeGen2Reg1ImmInstruction(ProcessorType processorType, char *instruction,
                                int reg1Index, int reg2Index, void *imm);
int codeGenConvertFromIntToFloat(int intRegIndex);
int codeGenConvertFromFloatToInt(int floatRegIndex);
void codeGenFPCmpInst(char *Inst, int Dist, int Op1, int Op2);
//*************************

void codeGenProgramNode(AST_NODE *programNode);
void codeGenGlobalVariable(AST_NODE *varaibleDeclListNode);
void codeGenFunctionDeclaration(AST_NODE *functionDeclNode);
void codeGenGeneralNode(AST_NODE *node);
void codeGenStmtNode(AST_NODE *stmtNode);
void codeGenBlockNode(AST_NODE *blockNode);
void codeGenWhileStmt(AST_NODE *whileStmtNode);
void codeGenForStmt(AST_NODE *forStmtNode);
void codeGenIfStmt(AST_NODE *ifStmtNode);
void codeGenReturnStmt(AST_NODE *returnStmtNode);
void codeGenAssignOrExpr(AST_NODE *testNode);
void codeGenAssignmentStmt(AST_NODE *assignmentStmtNode);
void codeGenExprRelatedNode(AST_NODE *exprRelatedNode);
void codeGenExprNode(AST_NODE *exprNode);
void codeGenFunctionCall(AST_NODE *functionCallNode);
void codeGenVariableReference(AST_NODE *idNode);
void codeGenConstantReference(AST_NODE *constantNode);
int codeGenCalcArrayElemenetAddress(AST_NODE *idNode);
    //Variable init
void codeGenDeclNode(AST_NODE *decl_node);
    //End Variable init
//Function parameters
void codeGenStoreParam(AST_NODE *traverseParameter, Parameter* formalParameter);
//End Function parameters


int getLabelNumber() {
  static int labelNumber = 0;
  return labelNumber++;
}

int codeGenConstantLabel(C_type constantType, void *valuePtr) {
  int labelNumber = getLabelNumber();

  fprintf(g_codeGenOutputFp, ".data\n");

  if (constantType == INTEGERC) {
    int *val = (int *)valuePtr;
    fprintf(g_codeGenOutputFp, "_CONSTANT_%d: .word %d\n", labelNumber, *val);
    fprintf(g_codeGenOutputFp, ".align 3\n");
  } else if (constantType == FLOATC) {
    float *val = (float *)valuePtr;
    fprintf(g_codeGenOutputFp, "_CONSTANT_%d: .float %f\n", labelNumber, *val);
    fprintf(g_codeGenOutputFp, ".align 3\n");
  } else if (constantType == STRINGC) {
    char *val;
    val = (char *)valuePtr;
    val[strlen(valuePtr) - 1] = '\0';
    fprintf(g_codeGenOutputFp, "_CONSTANT_%d: .ascii %s", labelNumber, val);
    fprintf(g_codeGenOutputFp, "\\000\"\n");
    fprintf(g_codeGenOutputFp, ".align 3\n");
    val[strlen(valuePtr) - 1] = '"';
    val[strlen(valuePtr)] = '\0';
  }

  fprintf(g_codeGenOutputFp, ".text\n");

  return labelNumber;
}

void codeGenSetReg(ProcessorType processorType, char *instruction,
                   int reg1Index, int value) {
  char *reg1Name = NULL;
  codeGenPrepareRegister(processorType, reg1Index, 0, 0, &reg1Name);
  fprintf(g_codeGenOutputFp, "%s %s, #%d\n", instruction, reg1Name, value);
  codeGenSaveToMemoryIfPsuedoRegister(processorType, reg1Index, reg1Name);
}

void codeGenSetReg_cond(ProcessorType processorType, char *instruction,
                        int reg1Index, char *cond) {
  char *reg1Name = NULL;
  codeGenPrepareRegister(processorType, reg1Index, 0, 0, &reg1Name);
  fprintf(g_codeGenOutputFp, "%s %s, %s\n", instruction, reg1Name, cond);
  codeGenSaveToMemoryIfPsuedoRegister(processorType, reg1Index, reg1Name);
}

void codeGenPrepareRegister_64(ProcessorType processorType, int regIndex,
                               int needToBeLoaded, int workRegIndexIfPseudo,
                               char **regName) {
  int realRegisterCount =
      (processorType == INT_REG) ? INT_REGISTER_COUNT : FLOAT_REGISTER_COUNT;
  char **realRegisterName =
      (processorType == INT_REG) ? intRegisterName_64 : floatRegisterName;
  char **workRegisterName = (processorType == INT_REG) ? intWorkRegisterName_64
                                                       : floatWorkRegisterName;
  char *loadInstruction = (processorType == INT_REG) ? "ld" : "fld";

  if (regIndex >= realRegisterCount) {
    // pseudo register
    int pseudoIndex = regIndex - realRegisterCount;
    *regName = workRegisterName[workRegIndexIfPseudo];
    if (needToBeLoaded) {
      fprintf(g_codeGenOutputFp, "%s %s,%d(fp)\n", loadInstruction, *regName,
              getPseudoRegisterCorrespondingOffset(pseudoIndex));
    }
  } else {
    *regName = realRegisterName[regIndex];
    g_intRegisterTable.is64[regIndex] = 1;
  }
}


//TODO: trasnlate to risc-v
void codeGenGetBoolOfFloat(int boolRegIndex, int floatRegIndex) {

  int zero = 0x0;
  int constantZeroLabelNumber = codeGenConstantLabel(INTEGERC, &zero);
  char *boolRegName = NULL;
  codeGenPrepareRegister(INT_REG, boolRegIndex, 0, 0, &boolRegName);

  char *tmpZeroRegName = intWorkRegisterName[0];
  fprintf(g_codeGenOutputFp, "ldr %s, =_CONSTANT_%d\n",
          intWorkRegisterName_64[1], constantZeroLabelNumber);
  fprintf(g_codeGenOutputFp, "ldr %s, [%s,#0]\n", tmpZeroRegName,
          intWorkRegisterName_64[1]);
  char *origFloatRegName = NULL;
  codeGenPrepareRegister(FLOAT_REG, floatRegIndex, 1, 1, &origFloatRegName);
  fprintf(g_codeGenOutputFp, "str %s, [%s,#0]\n", origFloatRegName,
          intWorkRegisterName_64[1]);
  fprintf(g_codeGenOutputFp, "ldr %s, [%s,#0]\n", boolRegName,
          intWorkRegisterName_64[1]);
  fprintf(g_codeGenOutputFp, "cmp %s, %s\n", tmpZeroRegName, boolRegName);

  char *reg1Name = NULL;
  fprintf(g_codeGenOutputFp, "cset %s, ne\n", boolRegName);

  codeGenSaveToMemoryIfPsuedoRegister(INT_REG, boolRegIndex, boolRegName);
}

void codeGenPrepareRegister(ProcessorType processorType, int regIndex,
                            int needToBeLoaded, int workRegIndexIfPseudo,
                            char **regName) {
  int realRegisterCount =
      (processorType == INT_REG) ? INT_REGISTER_COUNT : FLOAT_REGISTER_COUNT;
  char **realRegisterName;
  char **workRegisterName;
  char *loadInstruction = (processorType == INT_REG) ? "lw" : "flw";

  if (regIndex >= realRegisterCount) {
    // pseudo register
    realRegisterName =
        (processorType == INT_REG) ? intRegisterName : floatRegisterName;
    workRegisterName = (processorType == INT_REG) ? intWorkRegisterName
                                                  : floatWorkRegisterName;
    int pseudoIndex = regIndex - realRegisterCount;
    *regName = workRegisterName[workRegIndexIfPseudo];
    if (needToBeLoaded) {
      fprintf(g_codeGenOutputFp, "%s %s,%d(fp)\n", loadInstruction, *regName,
              getPseudoRegisterCorrespondingOffset(pseudoIndex));
    }
  } else {
    if (processorType == INT_REG) {
      if (g_intRegisterTable.is64[regIndex] == 1) {
        *regName = intRegisterName_64[regIndex];
      } else {
        *regName = intRegisterName[regIndex];
      }

    } else {
      realRegisterName = floatRegisterName;
      workRegisterName = floatWorkRegisterName;
      *regName = realRegisterName[regIndex];
    }
  }
}

void codeGenSaveToMemoryIfPsuedoRegister(ProcessorType processorType,
                                         int regIndex, char *regName) {
  int realRegisterCount =
      (processorType == INT_REG) ? INT_REGISTER_COUNT : FLOAT_REGISTER_COUNT;
  char *saveInstruction = (processorType == INT_REG) ? "sw" : "fsw";

  if (regIndex >= realRegisterCount) {
    // pseudo register
    int pseudoIndex = regIndex - realRegisterCount;
    fprintf(g_codeGenOutputFp, "%s %s,%d(fp)\n", saveInstruction, regName,
            getPseudoRegisterCorrespondingOffset(pseudoIndex));
  }
}

void codeGen1Reg1ImmInstruction(ProcessorType processorType, char *instruction,
                                int reg1Index, int *value) {
  char *reg1Name = NULL;
  codeGenPrepareRegister(processorType, reg1Index, 0, 0, &reg1Name);

  if (processorType == INT_REG) {
    fprintf(g_codeGenOutputFp, "%s %s, #%d\n", instruction, reg1Name,
            *((int *)value));
  }

  codeGenSaveToMemoryIfPsuedoRegister(processorType, reg1Index, reg1Name);
}

void codeGenLogicalInstruction(ProcessorType processorType, char *instruction,
                               int dstRegIndex, int srcReg1Index,
                               int srcReg2Index) {
  int boolReg1Index = -1;
  int boolReg2Index = -1;

  if (processorType == FLOAT_REG) {
    boolReg1Index = getRegister(INT_REG);
    boolReg2Index = getRegister(INT_REG);
    codeGenGetBoolOfFloat(boolReg1Index, srcReg1Index);
    codeGenGetBoolOfFloat(boolReg2Index, srcReg2Index);
  } else if (processorType == INT_REG) {
    boolReg1Index = srcReg1Index;
    boolReg2Index = srcReg2Index;
    codeGen2RegInstruction(INT_REG, "snez", boolReg1Index, srcReg1Index);
    codeGen2RegInstruction(INT_REG, "snez", boolReg2Index, srcReg2Index);
  }

  codeGen3RegInstruction(INT_REG, instruction, dstRegIndex, boolReg1Index,
                         boolReg2Index);

  if (processorType == FLOAT_REG) {
    freeRegister(INT_REG, boolReg1Index);
    freeRegister(INT_REG, boolReg2Index);
  }
}

void codeGenCmp0Instruction(ProcessorType processorType, char *instruction,
                            int reg1Index, int imm) {

  char *reg1Name = NULL;
  codeGenPrepareRegister(processorType, reg1Index, 0, 0, &reg1Name);
  fprintf(g_codeGenOutputFp, "%s %s, #%d\n", instruction, reg1Name, imm);
  codeGenSaveToMemoryIfPsuedoRegister(processorType, reg1Index, reg1Name);
}

void codeGen2RegInstruction(ProcessorType processorType, char *instruction,
                            int reg1Index, int reg2Index) {
  char *reg1Name = NULL;
  codeGenPrepareRegister(processorType, reg1Index, 0, 0, &reg1Name);

  char *reg2Name = NULL;
  codeGenPrepareRegister(processorType, reg2Index, 1, 1, &reg2Name);

  fprintf(g_codeGenOutputFp, "%s %s, %s\n", instruction, reg1Name, reg2Name);

  codeGenSaveToMemoryIfPsuedoRegister(processorType, reg1Index, reg1Name);
}

void codeGenFPCmpInst(char *Inst, int Dist, int Op1, int Op2) {
  char *DistName = NULL;
  char *Op1Name = NULL;
  char *Op2Name = NULL;
  codeGenPrepareRegister(INT_REG, Dist, 0, 0, &DistName);
  codeGenPrepareRegister(FLOAT_REG, Op1, 1, 0, &Op1Name);
  codeGenPrepareRegister(FLOAT_REG, Op2, 1, 1, &Op2Name);
  fprintf(g_codeGenOutputFp, "%s %s, %s, %s\n", Inst, DistName, Op1Name, Op2Name);
  codeGenSaveToMemoryIfPsuedoRegister(FLOAT_REG, Op1, Op1Name);
}

void codeGen3RegInstruction(ProcessorType processorType, char *instruction,
                            int reg1Index, int reg2Index, int reg3Index) {
  char *reg1Name = NULL;
  codeGenPrepareRegister(processorType, reg1Index, 0, 0, &reg1Name);

  char *reg2Name = NULL;
  codeGenPrepareRegister(processorType, reg2Index, 1, 0, &reg2Name);

  char *reg3Name = NULL;
  codeGenPrepareRegister(processorType, reg3Index, 1, 1, &reg3Name);

  fprintf(g_codeGenOutputFp, "%s %s, %s, %s\n", instruction, reg1Name, reg2Name,
          reg3Name);

  codeGenSaveToMemoryIfPsuedoRegister(processorType, reg1Index, reg1Name);
}

void codeGen2Reg1ImmInstruction_64(ProcessorType processorType,
                                   char *instruction, int reg1Index,
                                   int reg2Index, void *imm) {
  char *reg1Name = NULL;
  codeGenPrepareRegister_64(processorType, reg1Index, 0, 0, &reg1Name);

  char *reg2Name = NULL;
  codeGenPrepareRegister_64(processorType, reg2Index, 1, 0, &reg2Name);

  if (processorType == INT_REG) {
    int *val = (int *)imm;
    fprintf(g_codeGenOutputFp, "%s %s,%s,%d\n", instruction, reg1Name, reg2Name,
            *val);
  } else if (processorType == FLOAT_REG) {
    float *val = (float *)imm;
    fprintf(g_codeGenOutputFp, "%s %s, %s, %f\n", instruction, reg1Name,
            reg2Name, *val);
  }

  codeGenSaveToMemoryIfPsuedoRegister(processorType, reg1Index, reg1Name);
}

void codeGen2Reg1ImmInstruction(ProcessorType processorType, char *instruction,
                                int reg1Index, int reg2Index, void *imm) {
  char *reg1Name = NULL;
  codeGenPrepareRegister(processorType, reg1Index, 0, 0, &reg1Name);

  char *reg2Name = NULL;
  codeGenPrepareRegister(processorType, reg2Index, 1, 0, &reg2Name);

  if (processorType == INT_REG) {
    int *val = (int *)imm;
    fprintf(g_codeGenOutputFp, "%s %s, %s, #%d\n", instruction, reg1Name,
            reg2Name, *val);
  } else if (processorType == FLOAT_REG) {
    float *val = (float *)imm;
    fprintf(g_codeGenOutputFp, "%s %s, %s, %f\n", instruction, reg1Name,
            reg2Name, *val);
  }

  codeGenSaveToMemoryIfPsuedoRegister(processorType, reg1Index, reg1Name);
}


//Type conversion
int codeGenConvertFromIntToFloat(int intRegIndex) {
  int floatRegisterIndex = getRegister(FLOAT_REG);
  char *intRegisterName, *floatRegisterName;
  codeGenPrepareRegister(INT_REG, intRegIndex, 1, 0, &intRegisterName);
  codeGenPrepareRegister(FLOAT_REG, floatRegisterIndex, 0, 0, &floatRegisterName);
  fprintf(g_codeGenOutputFp, "fcvt.s.w %s, %s\n", floatRegisterName, intRegisterName);
  freeRegister(INT_REG, intRegIndex);
  return floatRegisterIndex;
}

int codeGenConvertFromFloatToInt(int floatRegIndex) {
  int intRegisterIndex = getRegister(INT_REG);
  char *intRegisterName, *floatRegisterName;
  codeGenPrepareRegister(INT_REG, intRegisterIndex, 1, 0, &intRegisterName);
  codeGenPrepareRegister(FLOAT_REG, floatRegIndex, 0, 0, &floatRegisterName);
  fprintf(g_codeGenOutputFp, "fcvt.w.s %s, %s\n", intRegisterName, floatRegisterName);
  freeRegister(FLOAT_REG, floatRegIndex);
  return intRegisterIndex;
}
//End Type conversion

void codeGenerate(AST_NODE *root) {
  char *outputfileName = "output.s";
  g_codeGenOutputFp = fopen(outputfileName, "w");
  if (!g_codeGenOutputFp) {
    printf("Cannot open file \"%s\"", outputfileName);
    exit(EXIT_FAILURE);
  }

  codeGenProgramNode(root);
}

void codeGenProgramNode(AST_NODE *programNode) {
  AST_NODE *traverseDeclaration = programNode->child;
  while (traverseDeclaration) {
    if (traverseDeclaration->nodeType == VARIABLE_DECL_LIST_NODE) {
      fprintf(g_codeGenOutputFp, ".data\n");
      codeGenGlobalVariable(traverseDeclaration);
      fprintf(g_codeGenOutputFp, ".text\n");
    } else if (traverseDeclaration->nodeType == DECLARATION_NODE) {
      codeGenFunctionDeclaration(traverseDeclaration);
    }
    traverseDeclaration = traverseDeclaration->rightSibling;
  }
  return;
}

void codeGenGlobalVariable(AST_NODE *varaibleDeclListNode) {
  AST_NODE *traverseDeclaration = varaibleDeclListNode->child;
  while (traverseDeclaration) {
    if (traverseDeclaration->semantic_value.declSemanticValue.kind ==
        VARIABLE_DECL) {
      AST_NODE *idNode = traverseDeclaration->child->rightSibling;
      while (idNode) {
        SymbolTableEntry *idSymbolTableEntry =
            idNode->semantic_value.identifierSemanticValue.symbolTableEntry;
        TypeDescriptor *idTypeDescriptor =
            idSymbolTableEntry->attribute->attr.typeDescriptor;

         //Variable init     
        float value = 0;
        if (id_kind(idNode) == WITH_INIT_ID) {
          value = const_type(idNode->child) == FLOATC ? const_fval(idNode->child) : const_ival(idNode->child);
        }

        if (idTypeDescriptor->kind == SCALAR_TYPE_DESCRIPTOR) {
          if (idTypeDescriptor->properties.dataType == INT_TYPE) {
            fprintf(g_codeGenOutputFp, "_g_%s: .word %d\n",
                    idSymbolTableEntry->name, (int)value);
          } else if (idTypeDescriptor->properties.dataType == FLOAT_TYPE) {
            fprintf(g_codeGenOutputFp, "_g_%s: .float %f\n",
                    idSymbolTableEntry->name, value);
          }
        } else if (idTypeDescriptor->kind == ARRAY_TYPE_DESCRIPTOR) {
          int variableSize = getVariableSize(idTypeDescriptor);
          fprintf(g_codeGenOutputFp, "_g_%s: .space %d\n",
                  idSymbolTableEntry->name, variableSize);
        }
        idNode = idNode->rightSibling;
        //End Variable init
      }
    }
    traverseDeclaration = traverseDeclaration->rightSibling;
  }
  return;
}

void codeGenFunctionDeclaration(AST_NODE *functionDeclNode) {
  AST_NODE *functionIdNode = functionDeclNode->child->rightSibling;
  int i;

  g_currentFunctionName =
      functionIdNode->semantic_value.identifierSemanticValue.identifierName;

  fprintf(g_codeGenOutputFp, ".text\n");
  if (strcmp(
          functionIdNode->semantic_value.identifierSemanticValue.identifierName,
          "main") != 0) {
    fprintf(
        g_codeGenOutputFp, "_start_%s:\n",
        functionIdNode->semantic_value.identifierSemanticValue.identifierName);
  } else {
    fprintf(
        g_codeGenOutputFp, "%s:\n",
        functionIdNode->semantic_value.identifierSemanticValue.identifierName);
  }

  // prologue
  fprintf(g_codeGenOutputFp, "sd ra,0(sp)\n");
  fprintf(g_codeGenOutputFp, "sd fp,-8(sp)\n");
  fprintf(g_codeGenOutputFp, "add fp,sp,-8\n");
  fprintf(g_codeGenOutputFp, "add sp,sp,-16\n");
  fprintf(
      g_codeGenOutputFp, "la ra,_frameSize_%s\n",
      functionIdNode->semantic_value.identifierSemanticValue.identifierName);
  fprintf(g_codeGenOutputFp, "lw ra,0(ra)\n");
  fprintf(g_codeGenOutputFp, "sub sp,sp,ra\n");
  printStoreRegister(g_codeGenOutputFp);

  resetRegisterTable(functionIdNode->semantic_value.identifierSemanticValue
                         .symbolTableEntry->attribute->offsetInAR);

  AST_NODE *blockNode = functionIdNode->rightSibling->rightSibling;
  AST_NODE *traverseListNode = blockNode->child;
  while (traverseListNode) {
    codeGenGeneralNode(traverseListNode);
    traverseListNode = traverseListNode->rightSibling;
  }

  // epilogue
  fprintf(g_codeGenOutputFp, "_end_%s:\n", g_currentFunctionName);
  printRestoreRegister(g_codeGenOutputFp);
  fprintf(g_codeGenOutputFp, "ld ra,8(fp)\n");
  fprintf(g_codeGenOutputFp, "mv sp,fp\n");
  fprintf(g_codeGenOutputFp, "add sp,sp,8\n");
  fprintf(g_codeGenOutputFp, "ld fp,0(fp)\n");
  if (strcmp(
          functionIdNode->semantic_value.identifierSemanticValue.identifierName,
          "main") == 0) {
  } else {
    fprintf(g_codeGenOutputFp, "jr ra\n");
  }
  fprintf(g_codeGenOutputFp, ".data\n");
  int frameSize =
      abs(functionIdNode->semantic_value.identifierSemanticValue
              .symbolTableEntry->attribute->offsetInAR) +
      (INT_REGISTER_COUNT + INT_WORK_REGISTER_COUNT + INT_OTHER_REGISTER_COUNT +
       FLOAT_REGISTER_COUNT + FLOAT_WORK_REGISTER_COUNT) *
          4 +
      g_pseudoRegisterTable.isAllocatedVector->size * 4;

  while (frameSize % 8 != 0) {
    frameSize = frameSize + 4;
  }
  frameSize = frameSize + (INT_REGISTER_COUNT + INT_WORK_REGISTER_COUNT +
                           INT_OTHER_REGISTER_COUNT) *
                              4;
  while (frameSize % 8 != 0) {
    frameSize = frameSize + 4;
  }
  fprintf(g_codeGenOutputFp, "_frameSize_%s: .word %d\n",
          functionIdNode->semantic_value.identifierSemanticValue.identifierName,
          frameSize + 8);
  return;
}

void codeGenBlockNode(AST_NODE *blockNode) {
  AST_NODE *traverseListNode = blockNode->child;
  while (traverseListNode) {
    codeGenGeneralNode(traverseListNode);
    traverseListNode = traverseListNode->rightSibling;
  }
}

void codeGenExprNode(AST_NODE *exprNode) {
  if (exprNode->semantic_value.exprSemanticValue.kind == BINARY_OPERATION) {
    AST_NODE *leftOp = exprNode->child;
    AST_NODE *rightOp = leftOp->rightSibling;
    codeGenExprRelatedNode(leftOp);
    codeGenExprRelatedNode(rightOp);
    if (leftOp->dataType == FLOAT_TYPE || rightOp->dataType == FLOAT_TYPE) {
      if (leftOp->dataType == INT_TYPE) {
        leftOp->registerIndex =
            codeGenConvertFromIntToFloat(leftOp->registerIndex);
      }
      if (rightOp->dataType == INT_TYPE) {
        rightOp->registerIndex =
            codeGenConvertFromIntToFloat(rightOp->registerIndex);
      }

      switch (exprNode->semantic_value.exprSemanticValue.op.binaryOp) {
      case BINARY_OP_ADD:
        exprNode->registerIndex = leftOp->registerIndex;
        codeGen3RegInstruction(FLOAT_REG, "fadd.s", exprNode->registerIndex,
                               leftOp->registerIndex, rightOp->registerIndex);
        break;
      case BINARY_OP_SUB:
        exprNode->registerIndex = leftOp->registerIndex;
        codeGen3RegInstruction(FLOAT_REG, "fsub.s", exprNode->registerIndex,
                               leftOp->registerIndex, rightOp->registerIndex);
        break;
      case BINARY_OP_MUL:
        exprNode->registerIndex = leftOp->registerIndex;
        codeGen3RegInstruction(FLOAT_REG, "fmul.s", exprNode->registerIndex,
                               leftOp->registerIndex, rightOp->registerIndex);
        break;
      case BINARY_OP_DIV:
        exprNode->registerIndex = leftOp->registerIndex;
        codeGen3RegInstruction(FLOAT_REG, "fdiv.s", exprNode->registerIndex,
                               leftOp->registerIndex, rightOp->registerIndex);
        break;
      case BINARY_OP_EQ:
        exprNode->registerIndex = getRegister(INT_REG);
        codeGenFPCmpInst("feq.s", exprNode->registerIndex,
                         leftOp->registerIndex, rightOp->registerIndex);
        freeRegister(FLOAT_REG, leftOp->registerIndex);
        break;
      case BINARY_OP_GE:
        exprNode->registerIndex = getRegister(INT_REG);
        codeGenFPCmpInst("fge.s", exprNode->registerIndex,
                         leftOp->registerIndex, rightOp->registerIndex);
        freeRegister(FLOAT_REG, leftOp->registerIndex);
        break;
      case BINARY_OP_LE:
        exprNode->registerIndex = getRegister(INT_REG);
        codeGenFPCmpInst("fle.s", exprNode->registerIndex,
                         leftOp->registerIndex, rightOp->registerIndex);
        freeRegister(FLOAT_REG, leftOp->registerIndex);
        break;
      case BINARY_OP_NE:
        exprNode->registerIndex = getRegister(INT_REG);
        codeGenFPCmpInst("feq.s", exprNode->registerIndex,
                         leftOp->registerIndex, rightOp->registerIndex);
        codeGen2RegInstruction(INT_REG, "seqz", exprNode->registerIndex,
                               exprNode->registerIndex);
        freeRegister(FLOAT_REG, leftOp->registerIndex);
        break;
      case BINARY_OP_GT:
        exprNode->registerIndex = getRegister(INT_REG);
        codeGenFPCmpInst("fgt.s", exprNode->registerIndex,
                         leftOp->registerIndex, rightOp->registerIndex);
        freeRegister(FLOAT_REG, leftOp->registerIndex);
        break;
      case BINARY_OP_LT:
        exprNode->registerIndex = getRegister(INT_REG);
        codeGenFPCmpInst("flt.s", exprNode->registerIndex,
                         leftOp->registerIndex, rightOp->registerIndex);
        freeRegister(FLOAT_REG, leftOp->registerIndex);
        break;
      case BINARY_OP_AND:
        exprNode->registerIndex = getRegister(INT_REG);
        codeGenLogicalInstruction(FLOAT_REG, "and", exprNode->registerIndex,
                                  leftOp->registerIndex,
                                  rightOp->registerIndex);
        freeRegister(FLOAT_REG, leftOp->registerIndex);
        break;
      case BINARY_OP_OR:
        exprNode->registerIndex = getRegister(INT_REG);
        codeGenLogicalInstruction(FLOAT_REG, "or", exprNode->registerIndex,
                                  leftOp->registerIndex,
                                  rightOp->registerIndex);
        freeRegister(FLOAT_REG, leftOp->registerIndex);
        break;
      default:
        printf(
            "Unhandled case in void evaluateExprValue(AST_NODE* exprNode)\n");
        break;
      }

      freeRegister(FLOAT_REG, rightOp->registerIndex);
    } else if (exprNode->dataType == INT_TYPE) {
      exprNode->registerIndex = leftOp->registerIndex;
      int tmp_reg_index;

      switch (exprNode->semantic_value.exprSemanticValue.op.binaryOp) {
      case BINARY_OP_ADD:
        codeGen3RegInstruction(INT_REG, "addw", exprNode->registerIndex,
                               leftOp->registerIndex, rightOp->registerIndex);
        break;
      case BINARY_OP_SUB:
        codeGen3RegInstruction(INT_REG, "subw", exprNode->registerIndex,
                               leftOp->registerIndex, rightOp->registerIndex);
        break;
      case BINARY_OP_MUL:
        codeGen3RegInstruction(INT_REG, "mulw", exprNode->registerIndex,
                               leftOp->registerIndex, rightOp->registerIndex);
        break;
      case BINARY_OP_DIV:
        codeGen3RegInstruction(INT_REG, "divw", exprNode->registerIndex,
                               leftOp->registerIndex, rightOp->registerIndex);
        break;
      case BINARY_OP_EQ:
        codeGen3RegInstruction(INT_REG, "sub", exprNode->registerIndex,
                               leftOp->registerIndex, rightOp->registerIndex);
        codeGen2RegInstruction(INT_REG, "seqz", exprNode->registerIndex,
                               exprNode->registerIndex);
        break;
      case BINARY_OP_GE:
        codeGen3RegInstruction(INT_REG, "slt", exprNode->registerIndex,
                               leftOp->registerIndex, rightOp->registerIndex);
        codeGen2RegInstruction(INT_REG, "seqz", exprNode->registerIndex,
                               exprNode->registerIndex);
        break;
      case BINARY_OP_LE:
        codeGen3RegInstruction(INT_REG, "sgt", exprNode->registerIndex,
                               leftOp->registerIndex, rightOp->registerIndex);
        codeGen2RegInstruction(INT_REG, "seqz", exprNode->registerIndex,
                               exprNode->registerIndex);
        break;
      case BINARY_OP_NE:
        codeGen3RegInstruction(INT_REG, "sub", exprNode->registerIndex,
                               leftOp->registerIndex, rightOp->registerIndex);
        codeGen2RegInstruction(INT_REG, "snez", exprNode->registerIndex,
                               exprNode->registerIndex);
        break;
      case BINARY_OP_GT:
        codeGen3RegInstruction(INT_REG, "sgt", exprNode->registerIndex,
                               leftOp->registerIndex, rightOp->registerIndex);

        break;
      case BINARY_OP_LT:
        codeGen3RegInstruction(INT_REG, "slt", exprNode->registerIndex,
                               leftOp->registerIndex, rightOp->registerIndex);
        break;
      case BINARY_OP_AND:
        codeGenLogicalInstruction(INT_REG, "and", exprNode->registerIndex,
                                  leftOp->registerIndex,
                                  rightOp->registerIndex);
        int labelNumber_ = getLabelNumber();

        int tmp_reg_index_ = getRegister(INT_REG);
        char *tmp_reg_name_ = NULL;  
        tmp_reg_name_ = intRegisterName_64[tmp_reg_index_]; 

        int tmp_reg2_index_;
        tmp_reg2_index_ = getRegister(INT_REG);
        char *tmp_reg2_name_ = NULL;
        tmp_reg2_name_ = intRegisterName_64[tmp_reg2_index_]; 

        char *leftOpName_ = intRegisterName_64[leftOp->registerIndex];
        char *rightOpName_ = intRegisterName_64[rightOp->registerIndex];   

        /*todo: short  circuit*/
        fprintf(g_codeGenOutputFp,"beqz %s, Then%d\n",leftOpName_, labelNumber_);

        fprintf(g_codeGenOutputFp,"beqz %s, Then%d\n",rightOpName_, labelNumber_);

        fprintf(g_codeGenOutputFp,"li %s, 1\n", leftOpName_);//the reg of false
        fprintf(g_codeGenOutputFp,"j Exit%d\n", labelNumber_);

        fprintf(g_codeGenOutputFp,"Then%d:\n", labelNumber_);
        fprintf(g_codeGenOutputFp,"li %s, 0\n", leftOpName_);//the reg of true

        fprintf(g_codeGenOutputFp,"Exit%d: \n",labelNumber_);

        /*freeRegister(INT_REG, tmp_reg_index_);
        freeRegister(INT_REG, tmp_reg2_index_);*/

        break;
      case BINARY_OP_OR:
        /*codeGenLogicalInstruction(INT_REG, "or", exprNode->registerIndex,
                                  leftOp->registerIndex,
                                  rightOp->registerIndex);*/
        /*char *reg1Name = NULL;
        codeGenPrepareRegister(processorType, reg1Index, 0, 0, &reg1Name);
        char *reg2Name = NULL;
        codeGenPrepareRegister(processorType, reg2Index, 1, 1, &reg2Name);
        //fprintf(g_codeGenOutputFp, "%s %s, %s\n", instruction, reg1Name, reg2Name);
        codeGenSaveToMemoryIfPsuedoRegister(processorType, reg1Index, reg1Name);*/
        //get label number constant
        //int labelNumber = getLabelNumber();
        //char *rightOpRegName = NULL;
        //int tmp_reg_index;
        tmp_reg_index = getRegister(INT_REG);
        char *tmp_reg_name = NULL;  
        //codeGenPrepareRegister(INT_REG, tmp_reg_index, 0, 0, &tmp_reg_name);  
        tmp_reg_name = intRegisterName_64[tmp_reg_index]; 

        int tmp_reg2_index;
        tmp_reg2_index = getRegister(INT_REG);
        char *tmp_reg2_name = NULL;
        //codeGenPrepareRegister(INT_REG, tmp_reg2_index, 1, 1, &tmp_reg2_name);
        tmp_reg2_name = intRegisterName_64[tmp_reg2_index]; 

        int labelNumber = getLabelNumber();

        char *leftOpName = intRegisterName_64[leftOp->registerIndex];
        char *rightOpName = intRegisterName_64[rightOp->registerIndex];   

        /*SymbolAttribute *leftAttribute = leftOp->semantic_value.identifierSemanticValue
                                     .symbolTableEntry->attribute;
        SymbolAttribute *rightAttribute = rightOp->semantic_value.identifierSemanticValue
                                     .symbolTableEntry->attribute;*/

        /*todo: short  circuit*/
        //fprintf(g_codeGenOutputFp, "li %s, fp, %d\n", leftOpName,leftOp->semantic_value.identifierSemanticValue.symbolTableEntry->attribute->offsetInAR);
        //printf("%d\n", leftOp->semantic_value.identifierSemanticValue.symbolTableEntry->attribute->offsetInAR);
        //fprintf(g_codeGenOutputFp, "addi %s, fp, %d\n", leftOpName, leftAttribute->offsetInAR);
        //fprintf(g_codeGenOutputFp,"lw %s, 0(%s)\n",leftOpName, leftOpName);
        fprintf(g_codeGenOutputFp,"bnez %s, Then%d\n",leftOpName, labelNumber);

        //fprintf(g_codeGenOutputFp, "la %s, fp, %d\n", rightOpName,rightOp->semantic_value.identifierSemanticValue.symbolTableEntry->attribute->offsetInAR);
        //fprintf(g_codeGenOutputFp, "addi %s, fp, %d\n", rightOpName, rightAttribute->offsetInAR);
        //fprintf(g_codeGenOutputFp,"lw %s, 0(%s)\n",rightOpName, rightOpName);
        fprintf(g_codeGenOutputFp,"bnez %s, Then%d\n",rightOpName, labelNumber);

        fprintf(g_codeGenOutputFp,"li %s, 0\n", leftOpName);//the reg of false
        fprintf(g_codeGenOutputFp,"j Exit%d\n", labelNumber);

        fprintf(g_codeGenOutputFp,"Then%d:\n", labelNumber);
        fprintf(g_codeGenOutputFp,"li %s, 1\n", leftOpName);//the reg of true

        fprintf(g_codeGenOutputFp,"Exit%d: \n",labelNumber);

        break;
      default:
        printf(
            "Unhandled case in void evaluateExprValue(AST_NODE* exprNode)\n");
        break;
      }

      freeRegister(INT_REG, rightOp->registerIndex);
    }
  } // endif BINARY_OPERATION
  else if (exprNode->semantic_value.exprSemanticValue.kind == UNARY_OPERATION) {
    int tmpZero = 0;
    AST_NODE *operand = exprNode->child;
    codeGenExprRelatedNode(operand);
    if (operand->dataType == FLOAT_TYPE) {
      switch (exprNode->semantic_value.exprSemanticValue.op.unaryOp) {
      case UNARY_OP_POSITIVE:
        exprNode->registerIndex = operand->registerIndex;
        break;
      case UNARY_OP_NEGATIVE:
        exprNode->registerIndex = operand->registerIndex;
        codeGen2RegInstruction(FLOAT_REG, "fneg.s", exprNode->registerIndex,
                               exprNode->registerIndex);
        break;
      case UNARY_OP_LOGICAL_NEGATION:
        exprNode->registerIndex = getRegister(INT_REG);
        codeGenGetBoolOfFloat(exprNode->registerIndex, operand->registerIndex);
        freeRegister(FLOAT_REG, operand->registerIndex);
        break;
      default:
        printf(
            "Unhandled case in void evaluateExprValue(AST_NODE* exprNode)\n");
        break;
      }
    } else if (operand->dataType == INT_TYPE) {
      switch (exprNode->semantic_value.exprSemanticValue.op.unaryOp) {
      case UNARY_OP_POSITIVE:
        exprNode->registerIndex = operand->registerIndex;
        break;
      case UNARY_OP_NEGATIVE:
        exprNode->registerIndex = operand->registerIndex;
        codeGen2RegInstruction(INT_REG, "neg", exprNode->registerIndex,
                               exprNode->registerIndex);
        break;
      case UNARY_OP_LOGICAL_NEGATION:
        exprNode->registerIndex = operand->registerIndex;
        codeGen2RegInstruction(INT_REG, "seqz", exprNode->registerIndex,
                               exprNode->registerIndex);
        break;
      default:
        printf(
            "Unhandled case in void evaluateExprValue(AST_NODE* exprNode)\n");
        break;
      }
    }
  }
}

void codeGenFunctionCall(AST_NODE *functionCallNode) {
  AST_NODE *functionIdNode = functionCallNode->child;
  AST_NODE *parameterList = functionIdNode->rightSibling;
  if (strcmp(
          functionIdNode->semantic_value.identifierSemanticValue.identifierName,
          "write") == 0) {
    AST_NODE *firstParameter = parameterList->child;
    codeGenExprRelatedNode(firstParameter);
    char *parameterRegName = NULL;
    switch (firstParameter->dataType) {
    case INT_TYPE:
      codeGenPrepareRegister(INT_REG, firstParameter->registerIndex, 1, 0,
                             &parameterRegName);
      fprintf(g_codeGenOutputFp, "mv a0,%s\n", parameterRegName);
      fprintf(g_codeGenOutputFp, "jal _write_int\n");
      freeRegister(INT_REG, firstParameter->registerIndex);
      break;
    case FLOAT_TYPE:
      codeGenPrepareRegister(FLOAT_REG, firstParameter->registerIndex, 1, 0,
                             &parameterRegName);
      fprintf(g_codeGenOutputFp, "fmv.s fa0,%s\n", parameterRegName);
      fprintf(g_codeGenOutputFp, "jal _write_float\n");
      freeRegister(FLOAT_REG, firstParameter->registerIndex);
      break;
    case CONST_STRING_TYPE:
      codeGenPrepareRegister(INT_REG, firstParameter->registerIndex, 1, 0,
                             &parameterRegName);
      fprintf(g_codeGenOutputFp, "mv a0,%s\n", parameterRegName);
      fprintf(g_codeGenOutputFp, "jal _write_str\n");
      freeRegister(INT_REG, firstParameter->registerIndex);
      break;
    default:
      printf("Unhandled case in void codeGenFunctionCall(AST_NODE* "
             "functionCallNode)\n");
      printf("firstParameter->registerIndex was not free\n");
      break;
    }
    return;
  }

  if (strcmp(
          functionIdNode->semantic_value.identifierSemanticValue.identifierName,
          "read") == 0) {
    fprintf(g_codeGenOutputFp, "jal _read_int\n");
  } else if (strcmp(functionIdNode->semantic_value.identifierSemanticValue
                        .identifierName,
                    "fread") == 0) {
    fprintf(g_codeGenOutputFp, "jal _read_float\n");
  } else {
    if (strcmp(functionIdNode->semantic_value.identifierSemanticValue
                   .identifierName,
               "main") != 0) {
      //Function parameters
      AST_NODE* traverseParameter = parameterList->child;
      codeGenStoreParam(traverseParameter, id_sym(functionIdNode)->attribute->attr.functionSignature->parameterList);
      fprintf(g_codeGenOutputFp, "jal _start_%s\n",
              functionIdNode->semantic_value.identifierSemanticValue
                  .identifierName);
      int paramOffset = 0;
      while(traverseParameter) {
        paramOffset += 8;
        traverseParameter = traverseParameter->rightSibling;
      }
      if (paramOffset > 0) {
        fprintf(g_codeGenOutputFp, "addi sp, sp, %d\n", paramOffset);
      }

      //End Function parameters
    } else {
      fprintf(g_codeGenOutputFp, "jal %s\n",
              functionIdNode->semantic_value.identifierSemanticValue
                  .identifierName);
    }
  }

  if (functionIdNode->semantic_value.identifierSemanticValue.symbolTableEntry) {
    if (functionIdNode->semantic_value.identifierSemanticValue.symbolTableEntry
            ->attribute->attr.functionSignature->returnType == INT_TYPE) {
      functionCallNode->registerIndex = getRegister(INT_REG);
      char *returnIntRegName = NULL;
      codeGenPrepareRegister(INT_REG, functionCallNode->registerIndex, 0, 0,
                             &returnIntRegName);

      fprintf(g_codeGenOutputFp, "mv %s, a0\n", returnIntRegName);

      codeGenSaveToMemoryIfPsuedoRegister(
          INT_REG, functionCallNode->registerIndex, returnIntRegName);
    } else if (functionIdNode->semantic_value.identifierSemanticValue
                   .symbolTableEntry->attribute->attr.functionSignature
                   ->returnType == FLOAT_TYPE) {
      functionCallNode->registerIndex = getRegister(FLOAT_REG);
      char *returnfloatRegName = NULL;
      codeGenPrepareRegister(FLOAT_REG, functionCallNode->registerIndex, 0, 0,
                             &returnfloatRegName);

      fprintf(g_codeGenOutputFp, "fmv.s %s,fa0\n", returnfloatRegName);

      codeGenSaveToMemoryIfPsuedoRegister(
          INT_REG, functionCallNode->registerIndex, returnfloatRegName);
    }
  }
}

//Function parameters
void codeGenStoreParam(AST_NODE *traverseParameter, Parameter* formalParameter)
{
  if (traverseParameter == NULL) {
    return;
  }
  codeGenStoreParam(traverseParameter->rightSibling, formalParameter->next);

  char* parameterRegName = NULL;
  if(traverseParameter->dataType == INT_TYPE) {
    codeGenExprRelatedNode(traverseParameter);
    
    if(formalParameter->type->properties.dataType == FLOAT_TYPE) {
      int floatIndex = codeGenConvertFromIntToFloat(traverseParameter->registerIndex);
      codeGenPrepareRegister(FLOAT_REG, floatIndex, 1, 0, &parameterRegName);
      fprintf(g_codeGenOutputFp, "sw %s, 0(sp)\n", parameterRegName);
      freeRegister(FLOAT_REG, floatIndex);
    } else {
      codeGenPrepareRegister(INT_REG, traverseParameter->registerIndex, 1, 0, &parameterRegName);
      fprintf(g_codeGenOutputFp, "sw %s, 0(sp)\n", parameterRegName);
      freeRegister(INT_REG, traverseParameter->registerIndex);
    }
  } else if(traverseParameter->dataType == FLOAT_TYPE) {
    codeGenExprRelatedNode(traverseParameter);

    if(formalParameter->type->properties.dataType == INT_TYPE) {
      int intIndex = codeGenConvertFromFloatToInt(traverseParameter->registerIndex);
      codeGenPrepareRegister(INT_REG, intIndex, 1, 0, &parameterRegName);
      fprintf(g_codeGenOutputFp, "sw %s, 0(sp)\n", parameterRegName);
      freeRegister(INT_REG, intIndex);
    } else {
      codeGenPrepareRegister(FLOAT_REG, traverseParameter->registerIndex, 1, 0, &parameterRegName);
      fprintf(g_codeGenOutputFp, "sw %s, 0(sp)\n", parameterRegName);
      freeRegister(FLOAT_REG, traverseParameter->registerIndex);
    }
  }
  fprintf(g_codeGenOutputFp, "add sp, sp, -8\n");
}
//End Function parameters

/*todo: Multiple dimensional arrays*/
int codeGenCalcArrayElemenetAddress(AST_NODE *idNode) {
  AST_NODE *traverseDim = idNode->child;
  int *sizeInEachDimension =
      idNode->semantic_value.identifierSemanticValue.symbolTableEntry->attribute
          ->attr.typeDescriptor->properties.arrayProperties.sizeInEachDimension;

  codeGenExprRelatedNode(traverseDim);
  int linearIdxRegisterIndex = traverseDim->registerIndex;
  traverseDim = traverseDim->rightSibling;
    
  int dimIndex = 1;
  /*TODO multiple dimensions*/
  char *offset_reg, *mul_reg, *expr_reg;
  int reg_index = getRegister(INT_REG);
  ArrayProperties array_prop = sym_typedesc(id_sym(idNode))->properties.arrayProperties;

  for (int dim = 1; dim < array_prop.dimension; dim++) {
    codeGenPrepareRegister(INT_REG, linearIdxRegisterIndex, 1, 0, &offset_reg);
    codeGenPrepareRegister(INT_REG, reg_index, 0, 1, &mul_reg);
    fprintf(g_codeGenOutputFp, "la %s, %d\n", mul_reg, sizeInEachDimension[dim]);
    fprintf(g_codeGenOutputFp, "mul %s, %s, %s\n", offset_reg, offset_reg, mul_reg);
    if (traverseDim != NULL) {
      codeGenExprRelatedNode(traverseDim);
      codeGenPrepareRegister(INT_REG, traverseDim->registerIndex, 1, 1, &expr_reg);
      fprintf(g_codeGenOutputFp, "add %s, %s, %s\n", offset_reg, offset_reg, expr_reg);
      freeRegister(INT_REG, traverseDim->registerIndex);
      traverseDim = traverseDim->rightSibling;
    }
   }

   freeRegister(INT_REG, reg_index);
  // char* output = NULL;
  // int d = 0;

  //   while(traverseDim)
  //   {
  //     int reg_index = getRegister(INT_REG);
  //     int reg_index2 = getRegister(INT_REG);
  //     idNode->registerIndex = getRegister(INT_REG);
  //     AST_NODE* dim = idNode->child;
  //     dim->registerIndex = getRegister(INT_REG);

  //     AST_NODE* dim_next = dim->rightSibling;
  //     dim_next->registerIndex = getRegister(INT_REG);

  //     char* dimRegName = NULL;
  //     char* dim_nextRegName = NULL;
  //     char* mul_reg = NULL;
  //     char* add_reg = NULL;

  //     /*fprintf(g_codeGenOutputFp, "la %s, _g_%s\n", intWorkRegisterName_64[0],
  //           idNode->semantic_value.identifierSemanticValue.identifierName);*/
  //     codeGenPrepareRegister(INT_REG, reg_index, 0, 1, &mul_reg);
  //     fprintf(g_codeGenOutputFp, "addi %s, x0, %d\n", mul_reg, sizeInEachDimension[d]);

  //     /*codeGenPrepareRegister(INT_REG, reg_index2, 0, 1, &add_reg);
  //     fprintf(g_codeGenOutputFp, "addi %s, x1, %d\n",add_reg, sizeInEachDimension[d+1]);*/

  //     codeGenPrepareRegister(INT_REG, dim->registerIndex, 1, 1, &dimRegName);
  //     fprintf(g_codeGenOutputFp, "mul %s, %s, %s\n", dimRegName, dimRegName, mul_reg);

  //     codeGenPrepareRegister(INT_REG, dim_next->registerIndex, 1, 1, &dim_nextRegName);
  //     fprintf(g_codeGenOutputFp,"add %s, %s, %s\n", dim_nextRegName, dim_nextRegName,intWorkRegisterName_64[0]);

  //     /*output*/
  //     output = dim_nextRegName;
  //     traverseDim = traverseDim -> rightSibling;
  //     d = d + 1;

  //   }

    // /*lw*/ 
    // fprintf(g_codeGenOutputFp, "lw %s, 0(%s)\n", output, output);

  int shiftLeftTwoBits = 2;
  codeGen2Reg1ImmInstruction_64(INT_REG, "sll", linearIdxRegisterIndex,
                                linearIdxRegisterIndex, &shiftLeftTwoBits);

  char *linearOffsetRegName = NULL;
  if (!isGlobalVariable(
          idNode->semantic_value.identifierSemanticValue.symbolTableEntry)) {
    int baseOffset = idNode->semantic_value.identifierSemanticValue
                         .symbolTableEntry->attribute->offsetInAR;
    codeGen2Reg1ImmInstruction_64(INT_REG, "add", linearIdxRegisterIndex,
                                  linearIdxRegisterIndex, &baseOffset);
    codeGenPrepareRegister_64(INT_REG, linearIdxRegisterIndex, 1, 0,
                              &linearOffsetRegName);
    fprintf(g_codeGenOutputFp, "add %s,%s,fp\n", linearOffsetRegName,
            linearOffsetRegName);
  } else {
    fprintf(g_codeGenOutputFp, "la %s, _g_%s\n", intWorkRegisterName_64[0],
            idNode->semantic_value.identifierSemanticValue.identifierName);
    codeGenPrepareRegister_64(INT_REG, linearIdxRegisterIndex, 1, 1,
                              &linearOffsetRegName);
    fprintf(g_codeGenOutputFp, "add %s,%s,%s\n", linearOffsetRegName,
            linearOffsetRegName, intWorkRegisterName_64[0]);
  }

  codeGenSaveToMemoryIfPsuedoRegister(INT_REG, linearIdxRegisterIndex,
                                      linearOffsetRegName);

  return linearIdxRegisterIndex;
}

void codeGenVariableReference(AST_NODE *idNode) {
  SymbolAttribute *idAttribute = idNode->semantic_value.identifierSemanticValue
                                     .symbolTableEntry->attribute;
  if (idNode->semantic_value.identifierSemanticValue.kind == NORMAL_ID) {
    if (idNode->dataType == INT_TYPE) {
      idNode->registerIndex = getRegister(INT_REG);
      char *loadRegName = NULL;
      if (!isGlobalVariable(idNode->semantic_value.identifierSemanticValue
                                .symbolTableEntry)) {
        codeGenPrepareRegister(INT_REG, idNode->registerIndex, 0, 0,
                               &loadRegName);
        fprintf(g_codeGenOutputFp, "lw %s,%d(fp)\n", loadRegName,
                idAttribute->offsetInAR);
      } else {
        fprintf(g_codeGenOutputFp, "la %s, _g_%s\n", intWorkRegisterName_64[0],
                idNode->semantic_value.identifierSemanticValue.identifierName);
        codeGenPrepareRegister(INT_REG, idNode->registerIndex, 0, 1,
                               &loadRegName);
        fprintf(g_codeGenOutputFp, "lw %s,0(%s)\n", loadRegName,
                intWorkRegisterName_64[0]);
      }
      codeGenSaveToMemoryIfPsuedoRegister(INT_REG, idNode->registerIndex,
                                          loadRegName);
    } else if (idNode->dataType == FLOAT_TYPE) {
      idNode->registerIndex = getRegister(FLOAT_REG);
      char *loadRegName = NULL;
      if (!isGlobalVariable(idNode->semantic_value.identifierSemanticValue
                                .symbolTableEntry)) {
        codeGenPrepareRegister(FLOAT_REG, idNode->registerIndex, 0, 0,
                               &loadRegName);
        fprintf(g_codeGenOutputFp, "flw %s,%d(fp)\n", loadRegName,
                idAttribute->offsetInAR);
      } else {
        fprintf(g_codeGenOutputFp, "la %s, _g_%s\n", intWorkRegisterName_64[0],
                idNode->semantic_value.identifierSemanticValue.identifierName);
        codeGenPrepareRegister(FLOAT_REG, idNode->registerIndex, 0, 0,
                               &loadRegName);
        fprintf(g_codeGenOutputFp, "flw %s,0(%s)\n", loadRegName,
                intWorkRegisterName_64[0]);
      }
      codeGenSaveToMemoryIfPsuedoRegister(FLOAT_REG, idNode->registerIndex,
                                          loadRegName);
    }
  } else if (idNode->semantic_value.identifierSemanticValue.kind == ARRAY_ID) {
    if (idNode->dataType == INT_TYPE || idNode->dataType == FLOAT_TYPE) {
      int elementAddressRegIndex = codeGenCalcArrayElemenetAddress(idNode);
      char *elementAddressRegName = NULL;
      codeGenPrepareRegister_64(INT_REG, elementAddressRegIndex, 1, 0,
                                &elementAddressRegName);

      if (idNode->dataType == INT_TYPE) {
        char *dstRegName = NULL;
        idNode->registerIndex = getRegister(INT_REG);
        codeGenPrepareRegister(INT_REG, idNode->registerIndex, 0, 0,
                               &dstRegName);
        fprintf(g_codeGenOutputFp, "lw %s,0(%s)\n", dstRegName,
                elementAddressRegName);
        freeRegister(INT_REG, elementAddressRegIndex);

        codeGenSaveToMemoryIfPsuedoRegister(INT_REG, idNode->registerIndex,
                                            dstRegName);
      } else if (idNode->dataType == FLOAT_TYPE) {
        char *dstRegName = NULL;
        idNode->registerIndex = getRegister(FLOAT_REG);
        codeGenPrepareRegister(FLOAT_REG, idNode->registerIndex, 0, 0,
                               &dstRegName);

        char *elementAddressRegName = NULL;
        codeGenPrepareRegister(INT_REG, elementAddressRegIndex, 1, 0,
                               &elementAddressRegName);

       fprintf(g_codeGenOutputFp, "flw %s,0(%s)\n", dstRegName,
                elementAddressRegName);
        codeGenSaveToMemoryIfPsuedoRegister(FLOAT_REG, idNode->registerIndex,
                                            dstRegName);

        freeRegister(INT_REG, elementAddressRegIndex);
      }
    }
  }
}

void codeGenConstantReference(AST_NODE *constantNode) {
  C_type cType = constantNode->semantic_value.const1->const_type;
  if (cType == INTEGERC) {
    int tmpInt = constantNode->semantic_value.const1->const_u.intval;
    int constantLabelNumber = codeGenConstantLabel(INTEGERC, &tmpInt);
    constantNode->registerIndex = getRegister(INT_REG);
    char *regName = NULL;
    codeGenPrepareRegister(INT_REG, constantNode->registerIndex, 0, 0,
                           &regName);
    fprintf(g_codeGenOutputFp, "lw %s, _CONSTANT_%d\n", regName,
            constantLabelNumber);
    codeGenSaveToMemoryIfPsuedoRegister(INT_REG, constantNode->registerIndex,
                                        regName);
  } else if (cType == FLOATC) {
    float tmpFloat = constantNode->semantic_value.const1->const_u.fval;
    int constantLabelNumber = codeGenConstantLabel(FLOATC, &tmpFloat);
    constantNode->registerIndex = getRegister(FLOAT_REG);
    char *regName = NULL;
    codeGenPrepareRegister(FLOAT_REG, constantNode->registerIndex, 0, 0,
                           &regName);
    fprintf(g_codeGenOutputFp, "la %s, _CONSTANT_%d\n",
            intWorkRegisterName_64[0], constantLabelNumber);
    fprintf(g_codeGenOutputFp, "flw %s,0(%s)\n", regName,
            intWorkRegisterName_64[0]);
    codeGenSaveToMemoryIfPsuedoRegister(FLOAT_REG, constantNode->registerIndex,
                                        regName);
  } else if (cType == STRINGC) {
    char *tmpCharPtr = constantNode->semantic_value.const1->const_u.sc;
    int constantLabelNumber = codeGenConstantLabel(STRINGC, tmpCharPtr);
    constantNode->registerIndex = getRegister(INT_REG);
    char *regName = NULL;
    codeGenPrepareRegister_64(INT_REG, constantNode->registerIndex, 0, 0,
                              &regName);
    fprintf(g_codeGenOutputFp, "la %s, _CONSTANT_%d\n", regName,
            constantLabelNumber);
    codeGenSaveToMemoryIfPsuedoRegister(INT_REG, constantNode->registerIndex,
                                        regName);
  }
}

void codeGenExprRelatedNode(AST_NODE *exprRelatedNode) {
  switch (exprRelatedNode->nodeType) {
  case EXPR_NODE:
    codeGenExprNode(exprRelatedNode);
    break;
  case STMT_NODE:
    codeGenFunctionCall(exprRelatedNode);
    break;
  case IDENTIFIER_NODE:
    codeGenVariableReference(exprRelatedNode);
    break;
  case CONST_VALUE_NODE:
    codeGenConstantReference(exprRelatedNode);
    break;
  default:
    printf("Unhandle case in void processExprRelatedNode(AST_NODE* "
           "exprRelatedNode)\n");
    exprRelatedNode->dataType = ERROR_TYPE;
    break;
  }
}

void codeGenAssignmentStmt(AST_NODE *assignmentStmtNode) {
  AST_NODE *leftOp = assignmentStmtNode->child;
  AST_NODE *rightOp = leftOp->rightSibling;
  codeGenExprRelatedNode(rightOp);

  //Type conversion
  if(leftOp->dataType == FLOAT_TYPE && rightOp->dataType == INT_TYPE)
  {
    rightOp->registerIndex = codeGenConvertFromIntToFloat(rightOp->registerIndex);
  }
  else if(leftOp->dataType == INT_TYPE && rightOp->dataType == FLOAT_TYPE) 
  {
    rightOp->registerIndex = codeGenConvertFromFloatToInt(rightOp->registerIndex);
  }
   //End Type conversion

  if (leftOp->semantic_value.identifierSemanticValue.kind == NORMAL_ID) {
    if (leftOp->dataType == INT_TYPE) {
      char *rightOpRegName = NULL;
      codeGenPrepareRegister(INT_REG, rightOp->registerIndex, 1, 0,
                             &rightOpRegName);
      if (!isGlobalVariable(leftOp->semantic_value.identifierSemanticValue
                                .symbolTableEntry)) {
        fprintf(g_codeGenOutputFp, "sw %s,%d(fp)\n", rightOpRegName,
                leftOp->semantic_value.identifierSemanticValue.symbolTableEntry
                    ->attribute->offsetInAR);
      } else {
        int tmp_reg_index = getRegister(INT_REG);
        char *tmp_reg_name = intRegisterName_64[tmp_reg_index];
        fprintf(g_codeGenOutputFp, "la %s, _g_%s\n", tmp_reg_name,
                leftOp->semantic_value.identifierSemanticValue.identifierName);
        fprintf(g_codeGenOutputFp, "sw %s,0(%s)\n", rightOpRegName,
                tmp_reg_name);
        freeRegister(INT_REG, tmp_reg_index);
      }
      leftOp->registerIndex = rightOp->registerIndex;
    } else if (leftOp->dataType == FLOAT_TYPE) {
      char *rightOpRegName = NULL;
      codeGenPrepareRegister(FLOAT_REG, rightOp->registerIndex, 1, 0,
                             &rightOpRegName);
      if (!isGlobalVariable(leftOp->semantic_value.identifierSemanticValue
                                .symbolTableEntry)) {
        fprintf(g_codeGenOutputFp, "fsw %s,%d(fp)\n", rightOpRegName,
                leftOp->semantic_value.identifierSemanticValue.symbolTableEntry
                    ->attribute->offsetInAR);
      } else {
        int tmp_reg_index = getRegister(INT_REG);
        char *tmp_reg_name = intRegisterName_64[tmp_reg_index];
        fprintf(g_codeGenOutputFp, "la %s, _g_%s\n", tmp_reg_name,
                leftOp->semantic_value.identifierSemanticValue.identifierName);
        fprintf(g_codeGenOutputFp, "fsw %s,0(%s)\n", rightOpRegName,
                tmp_reg_name);
        freeRegister(INT_REG, tmp_reg_index);
      }
      leftOp->registerIndex = rightOp->registerIndex;
    }
  } else if (leftOp->semantic_value.identifierSemanticValue.kind == ARRAY_ID) {
    int elementAddressRegIndex = codeGenCalcArrayElemenetAddress(leftOp);

    char *elementAddressRegName = NULL;
    codeGenPrepareRegister(INT_REG, elementAddressRegIndex, 1, 0,
                           &elementAddressRegName);
    if (leftOp->dataType == INT_TYPE) {
      char *rightOpRegName = NULL;
      codeGenPrepareRegister(INT_REG, rightOp->registerIndex, 1, 1,
                             &rightOpRegName);
      fprintf(g_codeGenOutputFp, "sw %s,0(%s)\n", rightOpRegName,
              elementAddressRegName);

      leftOp->registerIndex = rightOp->registerIndex;
    } else if (leftOp->dataType == FLOAT_TYPE) {
      char *rightOpRegName = NULL;
      codeGenPrepareRegister(FLOAT_REG, rightOp->registerIndex, 1, 0,
                             &rightOpRegName);

      fprintf(g_codeGenOutputFp, "fsw %s,0(%s)\n", rightOpRegName,
              elementAddressRegName);

      leftOp->registerIndex = rightOp->registerIndex;
    }

    freeRegister(INT_REG, elementAddressRegIndex);
  }
}

void codeGenAssignOrExpr(AST_NODE *testNode) {
  if (testNode->nodeType == STMT_NODE) {
    if (testNode->semantic_value.stmtSemanticValue.kind == ASSIGN_STMT) {
      codeGenAssignmentStmt(testNode);
    } else if (testNode->semantic_value.stmtSemanticValue.kind ==
               FUNCTION_CALL_STMT) {
      codeGenFunctionCall(testNode);
    }
  } else {
    codeGenExprRelatedNode(testNode);
  }
}

void codeGenWhileStmt(AST_NODE *whileStmtNode) {
  AST_NODE *boolExpression = whileStmtNode->child;

  int constantZeroLabelNumber = -1;
  if (boolExpression->dataType == FLOAT_TYPE) {
    float zero = 0.0f;
    constantZeroLabelNumber = codeGenConstantLabel(FLOATC, &zero);
  }

  int labelNumber = getLabelNumber();
  fprintf(g_codeGenOutputFp, "_whileTestLabel_%d:\n", labelNumber);

  codeGenAssignOrExpr(boolExpression);

  if (boolExpression->dataType == INT_TYPE) {
    char *boolRegName = NULL;
    codeGenPrepareRegister(INT_REG, boolExpression->registerIndex, 1, 0,
                           &boolRegName);
    fprintf(g_codeGenOutputFp, "beqz %s, _whileExitLabel_%d\n", boolRegName,
            labelNumber);
    freeRegister(INT_REG, boolExpression->registerIndex);
  } else if (boolExpression->dataType == FLOAT_TYPE) {
    fprintf(g_codeGenOutputFp, "la %s, _CONSTANT_%d\n",
            intWorkRegisterName_64[0], constantZeroLabelNumber);
    fprintf(g_codeGenOutputFp, "flw %s,0(%s)\n", floatWorkRegisterName[0],
            intWorkRegisterName_64[0]);

    char *boolRegName = NULL;
    codeGenPrepareRegister(FLOAT_REG, boolExpression->registerIndex, 1, 1,
                           &boolRegName);

    fprintf(g_codeGenOutputFp, "feq.s %s,%s,%s\n", intWorkRegisterName_64[0],
            boolRegName, floatWorkRegisterName[0]);
    fprintf(g_codeGenOutputFp, "bnez %s,_whileExitLabel_%d\n",
            intWorkRegisterName_64[0], labelNumber);
    freeRegister(FLOAT_REG, boolExpression->registerIndex);
  }

  AST_NODE *bodyNode = boolExpression->rightSibling;
  codeGenStmtNode(bodyNode);

  fprintf(g_codeGenOutputFp, "j _whileTestLabel_%d\n", labelNumber);
  fprintf(g_codeGenOutputFp, "_whileExitLabel_%d:\n", labelNumber);
}

void codeGenForStmt(AST_NODE *forStmtNode) 
{ 
  /*TODO*/
  AST_NODE* init = forStmtNode->child;
  AST_NODE* cond = init->rightSibling;
  AST_NODE* loop = cond->rightSibling;
  AST_NODE* block = loop->rightSibling;  
  AST_NODE* try = (cond->child)->child;

  int constantZeroLabelNumber = -1;
  if (init->dataType == FLOAT_TYPE) {
    float zero = 0.0f;
    constantZeroLabelNumber = codeGenConstantLabel(FLOATC, &zero);
  }

  int labelNumber = getLabelNumber();
  /*li sw*/
  AST_NODE* leftOp=(init->child)->child;
  char *rightOpRegName = NULL;
  int tmp_reg_index = getRegister(INT_REG);
  char *tmp_reg_name = intRegisterName_64[tmp_reg_index];
  fprintf(g_codeGenOutputFp, "li %s, %d\n", tmp_reg_name,leftOp->semantic_value.identifierSemanticValue.symbolTableEntry
                    ->attribute->offsetInAR);
  freeRegister(INT_REG, tmp_reg_index);

  fprintf(g_codeGenOutputFp, "_forTestLabel_%d:\n", labelNumber);

  codeGenExprNode(cond->child);

  if (try->dataType == INT_TYPE) {
    //printf("%s\n","hello");
    char *condRegName = NULL;
    codeGenPrepareRegister(INT_REG, cond->registerIndex, 1, 0,&condRegName);
    //printf("%s\n",condRegName);
    //fprintf(g_codeGenOutputFp, "slt %s, %s, %s\n", condRegName, condRegName);
    fprintf(g_codeGenOutputFp, "beqz %s,_forExitLabel_%d\n", condRegName, labelNumber);
    //freeRegister(INT_REG, cond->registerIndex);
  }else if(try->dataType == FLOAT_TYPE)/*not done*/
  {
    //printf("%s\n","hello2");
    char *condRegName = NULL;
    codeGenPrepareRegister(FLOAT_REG, cond->registerIndex, 1, 0,&condRegName);
    fprintf(g_codeGenOutputFp, "beqz %s,_forExitLabel_%d\n", condRegName, labelNumber);
    freeRegister(INT_REG, init->registerIndex);
  }

  fprintf(g_codeGenOutputFp, "j _forBodyLabel_%d\n", labelNumber);

  fprintf(g_codeGenOutputFp, "_forIncLabel_%d:\n", labelNumber);
  codeGenAssignmentStmt(loop->child);
  fprintf(g_codeGenOutputFp, "j _forTestLabel_%d\n", labelNumber);

  fprintf(g_codeGenOutputFp, "_forBodyLabel_%d:\n", labelNumber);
  codeGenStmtNode(block);
  fprintf(g_codeGenOutputFp, "j _forIncLabel_%d\n", labelNumber);
  
  fprintf(g_codeGenOutputFp, "_forExitLabel_%d:\n", labelNumber);
}

void codeGenIfStmt(AST_NODE *ifStmtNode) {
  AST_NODE *boolExpression = ifStmtNode->child;

  int constantZeroLabelNumber = -1;
  if (boolExpression->dataType == FLOAT_TYPE) {
    float zero = 0.0f;
    constantZeroLabelNumber = codeGenConstantLabel(FLOATC, &zero);
  }

  int labelNumber = getLabelNumber();

  codeGenAssignOrExpr(boolExpression);

  if (boolExpression->dataType == INT_TYPE) {
    char *boolRegName = NULL;
    codeGenPrepareRegister(INT_REG, boolExpression->registerIndex, 1, 0,
                           &boolRegName);
    fprintf(g_codeGenOutputFp, "beqz %s, _elseLabel_%d\n", boolRegName,
            labelNumber);
    freeRegister(INT_REG, boolExpression->registerIndex);
  } else if (boolExpression->dataType == FLOAT_TYPE) {
    fprintf(g_codeGenOutputFp, "ldr %s, _CONSTANT_%d\n",
            floatWorkRegisterName[0], constantZeroLabelNumber);
    char *boolRegName = NULL;
    codeGenPrepareRegister(FLOAT_REG, boolExpression->registerIndex, 1, 1,
                           &boolRegName);
    fprintf(g_codeGenOutputFp, "vcmp.f32 %s, %s\n", boolRegName,
            floatWorkRegisterName[0]);
    fprintf(g_codeGenOutputFp, "vmrs  APSR_nzcv, FPSCR\n");
    fprintf(g_codeGenOutputFp, "beq _whileExitLabel_%d\n", labelNumber);
    freeRegister(FLOAT_REG, boolExpression->registerIndex);
    codeGenPrepareRegister(FLOAT_REG, boolExpression->registerIndex, 1, 1,
                           &boolRegName);
  }

  AST_NODE *ifBodyNode = boolExpression->rightSibling;
  codeGenStmtNode(ifBodyNode);

  fprintf(g_codeGenOutputFp, "j _ifExitLabel_%d\n", labelNumber);
  fprintf(g_codeGenOutputFp, "_elseLabel_%d:\n", labelNumber);
  AST_NODE *elsePartNode = ifBodyNode->rightSibling;
  codeGenStmtNode(elsePartNode);
  fprintf(g_codeGenOutputFp, "_ifExitLabel_%d:\n", labelNumber);
}

void codeGenReturnStmt(AST_NODE *returnStmtNode) {
  AST_NODE *returnVal = returnStmtNode->child;
  if (returnVal->nodeType != NUL_NODE) {
    codeGenExprRelatedNode(returnVal);
    //Type conversion
     if(returnStmtNode->dataType == FLOAT_TYPE && returnVal->dataType == INT_TYPE)
    {
      returnVal->registerIndex = codeGenConvertFromIntToFloat(returnVal->registerIndex);
    }
    else if(returnStmtNode->dataType == INT_TYPE && returnVal->dataType == FLOAT_TYPE)
    {
      returnVal->registerIndex = codeGenConvertFromFloatToInt(returnVal->registerIndex);
    }
    //End Type conversion
   


    char *returnValRegName = NULL;
    if (returnVal->dataType == INT_TYPE) {
      codeGenPrepareRegister(INT_REG, returnVal->registerIndex, 1, 0,
                             &returnValRegName);
      fprintf(g_codeGenOutputFp, "mv a0,%s\n", returnValRegName);
      freeRegister(INT_REG, returnVal->registerIndex);
    } else if (returnVal->dataType == FLOAT_TYPE) {
      codeGenPrepareRegister(FLOAT_REG, returnVal->registerIndex, 1, 0,
                             &returnValRegName);
      fprintf(g_codeGenOutputFp, "fmv.s fa0,%s\n", returnValRegName);
      freeRegister(FLOAT_REG, returnVal->registerIndex);
    }
  }
  fprintf(g_codeGenOutputFp, "j _end_%s\n", g_currentFunctionName);
}

void codeGenStmtNode(AST_NODE *stmtNode) {
  // printSourceFile(g_codeGenOutputFp, stmtNode->linenumber);

  if (stmtNode->nodeType == NUL_NODE) {
    return;
  } else if (stmtNode->nodeType == BLOCK_NODE) {
    codeGenBlockNode(stmtNode);
  } else {
    switch (stmtNode->semantic_value.stmtSemanticValue.kind) {
    case WHILE_STMT:
      codeGenWhileStmt(stmtNode);
      break;
    case FOR_STMT:
      codeGenForStmt(stmtNode);
      break;
    case ASSIGN_STMT:
      codeGenAssignmentStmt(stmtNode);
      if (stmtNode->child->dataType == INT_TYPE) {
        freeRegister(INT_REG, stmtNode->child->registerIndex);
      } else if (stmtNode->child->dataType == FLOAT_TYPE) {
        freeRegister(FLOAT_REG, stmtNode->child->registerIndex);
      }
      break;
    case IF_STMT:
      codeGenIfStmt(stmtNode);
      break;
    case FUNCTION_CALL_STMT:
      codeGenFunctionCall(stmtNode);
      if (stmtNode->registerIndex != -1) {
        if (stmtNode->dataType == INT_TYPE) {
          freeRegister(INT_REG, stmtNode->registerIndex);
        } else if (stmtNode->dataType == FLOAT_TYPE) {
          freeRegister(FLOAT_REG, stmtNode->registerIndex);
        }
      }
      break;
    case RETURN_STMT:
      codeGenReturnStmt(stmtNode);
      break;
    default:
      printf("Unhandle case in void processStmtNode(AST_NODE* stmtNode)\n");
      break;
    }
  }
}

void codeGenGeneralNode(AST_NODE *node) {
  AST_NODE *traverseChildren = node->child;
  switch (node->nodeType) {
  case VARIABLE_DECL_LIST_NODE:
    //Variable init
      while(traverseChildren)
      {
        codeGenDeclNode(traverseChildren);
        traverseChildren = traverseChildren->rightSibling;
      }
    //End Variable init
    break;
  case STMT_LIST_NODE:
    while (traverseChildren) {
      codeGenStmtNode(traverseChildren);
      traverseChildren = traverseChildren->rightSibling;
    }
    break;
  case NONEMPTY_ASSIGN_EXPR_LIST_NODE:
    while (traverseChildren) {
      codeGenAssignOrExpr(traverseChildren);
      if (traverseChildren->rightSibling) {
        if (traverseChildren->dataType == INT_TYPE) {
          freeRegister(INT_REG, traverseChildren->registerIndex);
        } else if (traverseChildren->dataType == FLOAT_TYPE) {
          freeRegister(FLOAT_REG, traverseChildren->registerIndex);
        }
      }
      traverseChildren = traverseChildren->rightSibling;
    }
    node->registerIndex = traverseChildren->registerIndex;
    break;
  case NONEMPTY_RELOP_EXPR_LIST_NODE:
    while (traverseChildren) {
      codeGenExprRelatedNode(traverseChildren);
      if (traverseChildren->rightSibling) {
        if (traverseChildren->dataType == INT_TYPE) {
          freeRegister(INT_REG, traverseChildren->registerIndex);
        } else if (traverseChildren->dataType == FLOAT_TYPE) {
          freeRegister(FLOAT_REG, traverseChildren->registerIndex);
        }
      }
      traverseChildren = traverseChildren->rightSibling;
    }
    node->registerIndex = traverseChildren->registerIndex;
    break;
  case NUL_NODE:
    break;
  default:
    printf("Unhandle case in void processGeneralNode(AST_NODE *node)\n");
    node->dataType = ERROR_TYPE;
    break;
  }
}

    //Variable init

void codeGenDeclNode(AST_NODE *decl_node) {
  AST_NODE *id_node = decl_node->child->rightSibling;
  AST_NODE *typeNode = decl_node->child;
  while (id_node != NULL) {
    if (id_kind(id_node) == WITH_INIT_ID) {

      AST_NODE *constValueNode = id_node->child;
      if(typeNode->dataType == INT_TYPE) {
        int constValueIndex = getRegister(INT_REG);
        char *constValueRegName;
        int constantLabelNumber = codeGenConstantLabel(INTEGERC, &const_ival(constValueNode));

        codeGenPrepareRegister(INT_REG, constValueIndex, 0, 0, &constValueRegName);
        fprintf(g_codeGenOutputFp, "lw %s, _CONSTANT_%d\n", constValueRegName, constantLabelNumber);
        fprintf(g_codeGenOutputFp, "sw %s, %d(fp)\n", constValueRegName, id_sym(id_node)->attribute->offsetInAR);
        freeRegister(INT_REG, constValueIndex);
      } else if(typeNode->dataType == FLOAT_TYPE) {
        int constValueIndex = getRegister(FLOAT_REG);
        char *constValueRegName;
        int constantLabelNumber = codeGenConstantLabel(FLOATC, &const_fval(constValueNode));

        codeGenPrepareRegister(FLOAT_REG, constValueIndex, 0, 0, &constValueRegName);

        fprintf(g_codeGenOutputFp, "la %s, _CONSTANT_%d\n",intWorkRegisterName_64[0], constantLabelNumber);
        fprintf(g_codeGenOutputFp, "flw %s,0(%s)\n", constValueRegName, intWorkRegisterName_64[0]);
        fprintf(g_codeGenOutputFp, "fsw %s, %d(fp)\n", constValueRegName, id_sym(id_node)->attribute->offsetInAR);
        freeRegister(FLOAT_REG, constValueIndex);
      }
    }
    id_node = id_node->rightSibling;
  }
}
    //End Variable init
