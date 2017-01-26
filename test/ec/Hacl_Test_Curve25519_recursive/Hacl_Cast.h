/* This file auto-generated by KreMLin! */
#ifndef __Hacl_Cast_H
#define __Hacl_Cast_H


#include "Prims.h"
#include "FStar_Mul.h"
#include "FStar_Squash.h"
#include "FStar_StrongExcludedMiddle.h"
#include "FStar_List_Tot.h"
#include "FStar_Classical.h"
#include "FStar_ListProperties.h"
#include "FStar_Seq_Properties.h"
#include "FStar_Math_Lemmas.h"
#include "FStar_BitVector.h"
#include "FStar_UInt.h"
#include "FStar_Int.h"
#include "FStar_FunctionalExtensionality.h"
#include "FStar_PropositionalExtensionality.h"
#include "FStar_PredicateExtensionality.h"
#include "FStar_TSet.h"
#include "FStar_Set.h"
#include "FStar_Map.h"
#include "FStar_Ghost.h"
#include "FStar_All.h"
#include "Hacl_UInt64.h"
#include "Hacl_UInt128.h"
#include "Hacl_UInt32.h"
#include "Hacl_UInt8.h"
#include "kremlib.h"
#include "testlib.h"

FStar_UInt128_t Hacl_Cast_sint8_to_sint128(uint8_t a);

uint64_t Hacl_Cast_sint8_to_sint64(uint8_t a);

uint32_t Hacl_Cast_sint8_to_sint32(uint8_t a);

FStar_UInt128_t Hacl_Cast_sint32_to_sint128(uint32_t a);

uint64_t Hacl_Cast_sint32_to_sint64(uint32_t a);

uint8_t Hacl_Cast_sint32_to_sint8(uint32_t a);

FStar_UInt128_t Hacl_Cast_sint64_to_sint128(uint64_t a);

uint32_t Hacl_Cast_sint64_to_sint32(uint64_t a);

uint8_t Hacl_Cast_sint64_to_sint8(uint64_t a);

uint64_t Hacl_Cast_sint128_to_sint64(FStar_UInt128_t a);

uint32_t Hacl_Cast_sint128_to_sint32(FStar_UInt128_t a);

uint8_t Hacl_Cast_sint128_to_sint8(FStar_UInt128_t a);

FStar_UInt128_t Hacl_Cast_uint64_to_sint128(uint64_t a);

uint64_t Hacl_Cast_uint64_to_sint64(uint64_t a);

uint32_t Hacl_Cast_uint64_to_sint32(uint64_t a);

uint8_t Hacl_Cast_uint64_to_sint8(uint64_t a);

FStar_UInt128_t Hacl_Cast_uint32_to_sint128(uint32_t a);

uint64_t Hacl_Cast_uint32_to_sint64(uint32_t a);

uint32_t Hacl_Cast_uint32_to_sint32(uint32_t a);

uint8_t Hacl_Cast_uint32_to_sint8(uint32_t a);

FStar_UInt128_t Hacl_Cast_uint8_to_sint128(uint8_t a);

uint64_t Hacl_Cast_uint8_to_sint64(uint8_t a);

uint32_t Hacl_Cast_uint8_to_sint32(uint8_t a);

uint8_t Hacl_Cast_uint8_to_sint8(uint8_t a);
#endif
