# locations
UHCRULES_SRC_PREFIX						:= $(UHCRULES_TOP_PREFIX)src/
SRC_EHC_RULES_PREFIX					:= $(UHCRULES_SRC_PREFIX)ehc/rules/

# subdirs for pdflatex
EHC_SUBDIRS								:= $(patsubst $(UHCRULES_SRC_PREFIX)/%/,%,$(SRC_EHC_RULES_PREFIX))
LATEX_EHC_SUBDIRS						:= $(patsubst $(UHCRULES_SRC_PREFIX)%,%$(PATHS_SEP_COL),$(EHC_SUBDIRS))

# sources + dpds, for .rul
EHC_RULES_1_SRC_RUL						:= $(SRC_EHC_RULES_PREFIX)rules.rul
EHC_RULES_2_SRC_RUL						:= $(SRC_EHC_RULES_PREFIX)rules2.rul
EHC_RULES_3_SRC_RL2						:= $(SRC_EHC_RULES_PREFIX)EhcRulesOrig.rul

EHC_RULER_RULES							:= EHRulerRules
EHC_RULES_3_DRV_CAG						:= $(EHC_BLD_VARIANT_ASPECTS_PREFIX)$(EHC_RULER_RULES).cag
EHC_RULES_3_DRV_AG						:= $(EHC_RULES_3_DRV_CAG:.cag=.ag)

EHC_RULES_4_MAIN_SRC_RUL				:= $(patsubst %,$(SRC_EHC_RULES_PREFIX)%.rul,EhcRulesExpr2 EhcRulesTyMatch EhcRulesTyElimAlt)
EHC_RULES_4_DPDS_SRC_RUL				:= $(patsubst %,$(SRC_EHC_RULES_PREFIX)%.rul, \
													EhcRulesShared EhcRulesShared2 \
													EhcRulesAST EhcRulesCommon \
													EhcRulesRelations EhcRulesCommonSchemes EhcRulesSchemes EhcRulesSchemes2 \
											)
EHC_RULES_ALL_SRC						:= $(EHC_RULES_1_SRC_RUL) $(EHC_RULES_2_SRC_RUL) $(EHC_RULES_3_SRC_RL2) $(EHC_RULES_4_MAIN_SRC_RUL) $(EHC_RULES_4_DPDS_SRC_RUL)

