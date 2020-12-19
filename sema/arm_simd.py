simds = {
    "add": [
      "int16x8_t  vaddl_s8(int8x8_t a, int8x8_t b);      // VADDL.S8 q0,d0,d0 ",
      "int32x4_t  vaddl_s16(int16x4_t a, int16x4_t b);   // VADDL.S16 q0,d0,d0",
      "int64x2_t  vaddl_s32(int32x2_t a, int32x2_t b);   // VADDL.S32 q0,d0,d0",
      "uint16x8_t vaddl_u8(uint8x8_t a, uint8x8_t b);    // VADDL.U8 q0,d0,d0 ",
      "uint32x4_t vaddl_u16(uint16x4_t a, uint16x4_t b); // VADDL.U16 q0,d0,d0",
      "uint64x2_t vaddl_u32(uint32x2_t a, uint32x2_t b); // VADDL.U32 q0,d0,d0",
      "int16x8_t  vaddw_s8(int16x8_t a, int8x8_t b);     // VADDW.S8 q0,q0,d0",
      "int32x4_t  vaddw_s16(int32x4_t a, int16x4_t b);   // VADDW.S16 q0,q0,d0",
      "int64x2_t  vaddw_s32(int64x2_t a, int32x2_t b);   // VADDW.S32 q0,q0,d0",
      "uint16x8_t vaddw_u8(uint16x8_t a, uint8x8_t b);   // VADDW.U8 q0,q0,d0 ",
      "uint32x4_t vaddw_u16(uint32x4_t a, uint16x4_t b); // VADDW.U16 q0,q0,d0",
      "uint64x2_t vaddw_u32(uint64x2_t a, uint32x2_t b); // VADDW.U32 q0,q0,d0"
      ],
    "hadd": [
      "int8x8_t   vhadd_s8(int8x8_t a, int8x8_t b);       // VHADD.S8 d0,d0,d0 ",
      "int16x4_t  vhadd_s16(int16x4_t a, int16x4_t b);    // VHADD.S16 d0,d0,d0",
      "int32x2_t  vhadd_s32(int32x2_t a, int32x2_t b);    // VHADD.S32 d0,d0,d0",
      "uint8x8_t  vhadd_u8(uint8x8_t a, uint8x8_t b);     // VHADD.U8 d0,d0,d0 ",
      "uint16x4_t vhadd_u16(uint16x4_t a, uint16x4_t b);  // VHADD.U16 d0,d0,d0",
      "uint32x2_t vhadd_u32(uint32x2_t a, uint32x2_t b);  // VHADD.U32 d0,d0,d0",
      "int8x16_t  vhaddq_s8(int8x16_t a, int8x16_t b);    // VHADD.S8 q0,q0,q0 ",
      "int16x8_t  vhaddq_s16(int16x8_t a, int16x8_t b);   // VHADD.S16 q0,q0,q0",
      "int32x4_t  vhaddq_s32(int32x4_t a, int32x4_t b);   // VHADD.S32 q0,q0,q0",
      "uint8x16_t vhaddq_u8(uint8x16_t a, uint8x16_t b);  // VHADD.U8 q0,q0,q0 ",
      "uint16x8_t vhaddq_u16(uint16x8_t a, uint16x8_t b); // VHADD.U16 q0,q0,q0",
      "uint32x4_t vhaddq_u32(uint32x4_t a, uint32x4_t b); // VHADD.U32 q0,q0,q0"
      ],
    "rhadd": [
      "int8x8_t   vrhadd_s8(int8x8_t a, int8x8_t b);       // VRHADD.S8 d0,d0,d0 ",
      "int16x4_t  vrhadd_s16(int16x4_t a, int16x4_t b);    // VRHADD.S16 d0,d0,d0",
      "int32x2_t  vrhadd_s32(int32x2_t a, int32x2_t b);    // VRHADD.S32 d0,d0,d0",
      "uint8x8_t  vrhadd_u8(uint8x8_t a, uint8x8_t b);     // VRHADD.U8 d0,d0,d0 ",
      "uint16x4_t vrhadd_u16(uint16x4_t a, uint16x4_t b);  // VRHADD.U16 d0,d0,d0",
      "uint32x2_t vrhadd_u32(uint32x2_t a, uint32x2_t b);  // VRHADD.U32 d0,d0,d0",
      "int8x16_t  vrhaddq_s8(int8x16_t a, int8x16_t b);    // VRHADD.S8 q0,q0,q0 ",
      "int16x8_t  vrhaddq_s16(int16x8_t a, int16x8_t b);   // VRHADD.S16 q0,q0,q0",
      "int32x4_t  vrhaddq_s32(int32x4_t a, int32x4_t b);   // VRHADD.S32 q0,q0,q0",
      "uint8x16_t vrhaddq_u8(uint8x16_t a, uint8x16_t b);  // VRHADD.U8 q0,q0,q0 ",
      "uint16x8_t vrhaddq_u16(uint16x8_t a, uint16x8_t b); // VRHADD.U16 q0,q0,q0",
      "uint32x4_t vrhaddq_u32(uint32x4_t a, uint32x4_t b); // VRHADD.U32 q0,q0,q0"
      ],
    "qadd":[
      "int8x8_t   vqadd_s8(int8x8_t a, int8x8_t b);       // VQADD.S8 d0,d0,d0 ",
      "int16x4_t  vqadd_s16(int16x4_t a, int16x4_t b);    // VQADD.S16 d0,d0,d0",
      "int32x2_t  vqadd_s32(int32x2_t a, int32x2_t b);    // VQADD.S32 d0,d0,d0",
      "int64x1_t  vqadd_s64(int64x1_t a, int64x1_t b);    // VQADD.S64 d0,d0,d0",
      "uint8x8_t  vqadd_u8(uint8x8_t a, uint8x8_t b);     // VQADD.U8 d0,d0,d0 ",
      "uint16x4_t vqadd_u16(uint16x4_t a, uint16x4_t b);  // VQADD.U16 d0,d0,d0",
      "uint32x2_t vqadd_u32(uint32x2_t a, uint32x2_t b);  // VQADD.U32 d0,d0,d0",
      "uint64x1_t vqadd_u64(uint64x1_t a, uint64x1_t b);  // VQADD.U64 d0,d0,d0",
      "int8x16_t  vqaddq_s8(int8x16_t a, int8x16_t b);    // VQADD.S8 q0,q0,q0 ",
      "int16x8_t  vqaddq_s16(int16x8_t a, int16x8_t b);   // VQADD.S16 q0,q0,q0",
      "int32x4_t  vqaddq_s32(int32x4_t a, int32x4_t b);   // VQADD.S32 q0,q0,q0",
      "int64x2_t  vqaddq_s64(int64x2_t a, int64x2_t b);   // VQADD.S64 q0,q0,q0",
      "uint8x16_t vqaddq_u8(uint8x16_t a, uint8x16_t b);  // VQADD.U8 q0,q0,q0 ",
      "uint16x8_t vqaddq_u16(uint16x8_t a, uint16x8_t b); // VQADD.U16 q0,q0,q0",
      "uint32x4_t vqaddq_u32(uint32x4_t a, uint32x4_t b); // VQADD.U32 q0,q0,q0",
      "uint64x2_t vqaddq_u64(uint64x2_t a, uint64x2_t b); // VQADD.U64 q0,q0,q0"
      ],
    "addhn" : [
        "int8x8_t   vaddhn_s16(int16x8_t a, int16x8_t b);   // VADDHN.I16 d0,q0,q0",
        "int16x4_t  vaddhn_s32(int32x4_t a, int32x4_t b);   // VADDHN.I32 d0,q0,q0",
        "int32x2_t  vaddhn_s64(int64x2_t a, int64x2_t b);   // VADDHN.I64 d0,q0,q0",
        "uint8x8_t  vaddhn_u16(uint16x8_t a, uint16x8_t b); // VADDHN.I16 d0,q0,q0",
        "uint16x4_t vaddhn_u32(uint32x4_t a, uint32x4_t b); // VADDHN.I32 d0,q0,q0",
        "uint32x2_t vaddhn_u64(uint64x2_t a, uint64x2_t b); // VADDHN.I64 d0,q0,q0"
        ],
    "raddhn": [
        "int8x8_t   vraddhn_s16(int16x8_t a, int16x8_t b);   // VRADDHN.I16 d0,q0,q0",
        "int16x4_t  vraddhn_s32(int32x4_t a, int32x4_t b);   // VRADDHN.I32 d0,q0,q0",
        "int32x2_t  vraddhn_s64(int64x2_t a, int64x2_t b);   // VRADDHN.I64 d0,q0,q0",
        "uint8x8_t  vraddhn_u16(uint16x8_t a, uint16x8_t b); // VRADDHN.I16 d0,q0,q0",
        "uint16x4_t vraddhn_u32(uint32x4_t a, uint32x4_t b); // VRADDHN.I32 d0,q0,q0",
        "uint32x2_t vraddhn_u64(uint64x2_t a, uint64x2_t b); // VRADDHN.I64 d0,q0,q0"
        ],
    "mul": [
        "int8x8_t    vmul_s8(int8x8_t a, int8x8_t b);         // VMUL.I8 d0,d0,d0 ",
        "int16x4_t   vmul_s16(int16x4_t a, int16x4_t b);      // VMUL.I16 d0,d0,d0",
        "int32x2_t   vmul_s32(int32x2_t a, int32x2_t b);      // VMUL.I32 d0,d0,d0",
        "float32x2_t vmul_f32(float32x2_t a, float32x2_t b);  // VMUL.F32 d0,d0,d0",
        "uint8x8_t   vmul_u8(uint8x8_t a, uint8x8_t b);       // VMUL.I8 d0,d0,d0 ",
        "uint16x4_t  vmul_u16(uint16x4_t a, uint16x4_t b);    // VMUL.I16 d0,d0,d0",
        "uint32x2_t  vmul_u32(uint32x2_t a, uint32x2_t b);    // VMUL.I32 d0,d0,d0",
        "int8x16_t   vmulq_s8(int8x16_t a, int8x16_t b);      // VMUL.I8 q0,q0,q0 ",
        "int16x8_t   vmulq_s16(int16x8_t a, int16x8_t b);     // VMUL.I16 q0,q0,q0",
        "int32x4_t   vmulq_s32(int32x4_t a, int32x4_t b);     // VMUL.I32 q0,q0,q0",
        "float32x4_t vmulq_f32(float32x4_t a, float32x4_t b); // VMUL.F32 q0,q0,q0",
        "uint8x16_t  vmulq_u8(uint8x16_t a, uint8x16_t b);    // VMUL.I8 q0,q0,q0 ",
        "uint16x8_t  vmulq_u16(uint16x8_t a, uint16x8_t b);   // VMUL.I16 q0,q0,q0",
        "uint32x4_t  vmulq_u32(uint32x4_t a, uint32x4_t b);   // VMUL.I32 q0,q0,q0",
        "int16x8_t  vmull_s8(int8x8_t a, int8x8_t b);      // VMULL.S8 q0,d0,d0 ",
        "int32x4_t  vmull_s16(int16x4_t a, int16x4_t b);   // VMULL.S16 q0,d0,d0",
        "int64x2_t  vmull_s32(int32x2_t a, int32x2_t b);   // VMULL.S32 q0,d0,d0",
        "uint16x8_t vmull_u8(uint8x8_t a, uint8x8_t b);    // VMULL.U8 q0,d0,d0 ",
        "uint32x4_t vmull_u16(uint16x4_t a, uint16x4_t b); // VMULL.U16 q0,d0,d0",
        "uint64x2_t vmull_u32(uint32x2_t a, uint32x2_t b); // VMULL.U32 q0,d0,d0"
        ],
    "mla": [
        "int8x8_t    vmla_s8(int8x8_t a, int8x8_t b, int8x8_t c);        // VMLA.I8 d0,d0,d0 ",
        "int16x4_t   vmla_s16(int16x4_t a, int16x4_t b, int16x4_t c);    // VMLA.I16 d0,d0,d0",
        "int32x2_t   vmla_s32(int32x2_t a, int32x2_t b, int32x2_t c);    // VMLA.I32 d0,d0,d0",
        "float32x2_t vmla_f32(float32x2_t a, float32x2_t b, float32x2_t c);  // VMLA.F32 d0,d0,d0",
        "uint8x8_t   vmla_u8(uint8x8_t a, uint8x8_t b, uint8x8_t c);     // VMLA.I8 d0,d0,d0 ",
        "uint16x4_t  vmla_u16(uint16x4_t a, uint16x4_t b, uint16x4_t c); // VMLA.I16 d0,d0,d0",
        "uint32x2_t  vmla_u32(uint32x2_t a, uint32x2_t b, uint32x2_t c); // VMLA.I32 d0,d0,d0",
        "int8x16_t   vmlaq_s8(int8x16_t a, int8x16_t b, int8x16_t c);    // VMLA.I8 q0,q0,q0 ",
        "int16x8_t   vmlaq_s16(int16x8_t a, int16x8_t b, int16x8_t c);   // VMLA.I16 q0,q0,q0",
        "int32x4_t   vmlaq_s32(int32x4_t a, int32x4_t b, int32x4_t c);   // VMLA.I32 q0,q0,q0",
        "float32x4_t vmlaq_f32(float32x4_t a, float32x4_t b, float32x4_t c); // VMLA.F32 q0,q0,q0",
        "uint8x16_t  vmlaq_u8(uint8x16_t a, uint8x16_t b, uint8x16_t c); // VMLA.I8 q0,q0,q0 ",
        "uint16x8_t  vmlaq_u16(uint16x8_t a, uint16x8_t b, uint16x8_t c);// VMLA.I16 q0,q0,q0",
        "uint32x4_t  vmlaq_u32(uint32x4_t a, uint32x4_t b, uint32x4_t c);// VMLA.I32 q0,q0,q0",
        "int16x8_t  vmlal_s8(int16x8_t a, int8x8_t b, int8x8_t c);       // VMLAL.S8 q0,d0,d0 ",
        "int32x4_t  vmlal_s16(int32x4_t a, int16x4_t b, int16x4_t c);    // VMLAL.S16 q0,d0,d0",
        "int64x2_t  vmlal_s32(int64x2_t a, int32x2_t b, int32x2_t c);    // VMLAL.S32 q0,d0,d0",
        "uint16x8_t vmlal_u8(uint16x8_t a, uint8x8_t b, uint8x8_t c);    // VMLAL.U8 q0,d0,d0 ",
        "uint32x4_t vmlal_u16(uint32x4_t a, uint16x4_t b, uint16x4_t c); // VMLAL.U16 q0,d0,d0",
        "uint64x2_t vmlal_u32(uint64x2_t a, uint32x2_t b, uint32x2_t c); // VMLAL.U32 q0,d0,d0"
        ],
    "mls": [
        "int8x8_t    vmls_s8(int8x8_t a, int8x8_t b, int8x8_t c);        // VMLS.I8 d0,d0,d0 ",
        "int16x4_t   vmls_s16(int16x4_t a, int16x4_t b, int16x4_t c);    // VMLS.I16 d0,d0,d0",
        "int32x2_t   vmls_s32(int32x2_t a, int32x2_t b, int32x2_t c);    // VMLS.I32 d0,d0,d0",
        "float32x2_t vmls_f32(float32x2_t a, float32x2_t b, float32x2_t c); // VMLS.F32 d0,d0,d0",
        "uint8x8_t   vmls_u8(uint8x8_t a, uint8x8_t b, uint8x8_t c);     // VMLS.I8 d0,d0,d0 ",
        "uint16x4_t  vmls_u16(uint16x4_t a, uint16x4_t b, uint16x4_t c); // VMLS.I16 d0,d0,d0",
        "uint32x2_t  vmls_u32(uint32x2_t a, uint32x2_t b, uint32x2_t c); // VMLS.I32 d0,d0,d0",
        "int8x16_t   vmlsq_s8(int8x16_t a, int8x16_t b, int8x16_t c);    // VMLS.I8 q0,q0,q0 ",
        "int16x8_t   vmlsq_s16(int16x8_t a, int16x8_t b, int16x8_t c);   // VMLS.I16 q0,q0,q0",
        "int32x4_t   vmlsq_s32(int32x4_t a, int32x4_t b, int32x4_t c);   // VMLS.I32 q0,q0,q0",
        "float32x4_t vmlsq_f32(float32x4_t a, float32x4_t b, float32x4_t c); // VMLS.F32 q0,q0,q0",
        "uint8x16_t  vmlsq_u8(uint8x16_t a, uint8x16_t b, uint8x16_t c); // VMLS.I8 q0,q0,q0 ",
        "uint16x8_t  vmlsq_u16(uint16x8_t a, uint16x8_t b, uint16x8_t c);// VMLS.I16 q0,q0,q0",
        "uint32x4_t  vmlsq_u32(uint32x4_t a, uint32x4_t b, uint32x4_t c);// VMLS.I32 q0,q0,q0",
        "int16x8_t  vmlsl_s8(int16x8_t a, int8x8_t b, int8x8_t c);       // VMLSL.S8 q0,d0,d0 ",
        "int32x4_t  vmlsl_s16(int32x4_t a, int16x4_t b, int16x4_t c);    // VMLSL.S16 q0,d0,d0",
        "int64x2_t  vmlsl_s32(int64x2_t a, int32x2_t b, int32x2_t c);    // VMLSL.S32 q0,d0,d0",
        "uint16x8_t vmlsl_u8(uint16x8_t a, uint8x8_t b, uint8x8_t c);    // VMLSL.U8 q0,d0,d0 ",
        "uint32x4_t vmlsl_u16(uint32x4_t a, uint16x4_t b, uint16x4_t c); // VMLSL.U16 q0,d0,d0",
        "uint64x2_t vmlsl_u32(uint64x2_t a, uint32x2_t b, uint32x2_t c); // VMLSL.U32 q0,d0,d0"
        ],
    "qdmulh": [
        "int16x4_t vqdmulh_s16(int16x4_t a, int16x4_t b);  // VQDMULH.S16 d0,d0,d0",
        "int32x2_t vqdmulh_s32(int32x2_t a, int32x2_t b);  // VQDMULH.S32 d0,d0,d0",
        "int16x8_t vqdmulhq_s16(int16x8_t a, int16x8_t b); // VQDMULH.S16 q0,q0,q0",
        "int32x4_t vqdmulhq_s32(int32x4_t a, int32x4_t b); // VQDMULH.S32 q0,q0,q0"
        ],
    "qrdmulh": [
        "int16x4_t vqrdmulh_s16(int16x4_t a, int16x4_t b);  // VQRDMULH.S16 d0,d0,d0",
        "int32x2_t vqrdmulh_s32(int32x2_t a, int32x2_t b);  // VQRDMULH.S32 d0,d0,d0",
        "int16x8_t vqrdmulhq_s16(int16x8_t a, int16x8_t b); // VQRDMULH.S16 q0,q0,q0",
        "int32x4_t vqrdmulhq_s32(int32x4_t a, int32x4_t b); // VQRDMULH.S32 q0,q0,q0"
        ],
    "sub": [
        "int8x8_t    vsub_s8(int8x8_t a, int8x8_t b);         // VSUB.I8 d0,d0,d0 ",
        "int16x4_t   vsub_s16(int16x4_t a, int16x4_t b);      // VSUB.I16 d0,d0,d0",
        "int32x2_t   vsub_s32(int32x2_t a, int32x2_t b);      // VSUB.I32 d0,d0,d0",
        "int64x1_t   vsub_s64(int64x1_t a, int64x1_t b);      // VSUB.I64 d0,d0,d0",
        "float32x2_t vsub_f32(float32x2_t a, float32x2_t b);  // VSUB.F32 d0,d0,d0",
        "uint8x8_t   vsub_u8(uint8x8_t a, uint8x8_t b);       // VSUB.I8 d0,d0,d0 ",
        "uint16x4_t  vsub_u16(uint16x4_t a, uint16x4_t b);    // VSUB.I16 d0,d0,d0",
        "uint32x2_t  vsub_u32(uint32x2_t a, uint32x2_t b);    // VSUB.I32 d0,d0,d0",
        "uint64x1_t  vsub_u64(uint64x1_t a, uint64x1_t b);    // VSUB.I64 d0,d0,d0",
        "int8x16_t   vsubq_s8(int8x16_t a, int8x16_t b);      // VSUB.I8 q0,q0,q0 ",
        "int16x8_t   vsubq_s16(int16x8_t a, int16x8_t b);     // VSUB.I16 q0,q0,q0",
        "int32x4_t   vsubq_s32(int32x4_t a, int32x4_t b);     // VSUB.I32 q0,q0,q0",
        "int64x2_t   vsubq_s64(int64x2_t a, int64x2_t b);     // VSUB.I64 q0,q0,q0",
        "float32x4_t vsubq_f32(float32x4_t a, float32x4_t b); // VSUB.F32 q0,q0,q0",
        "uint8x16_t  vsubq_u8(uint8x16_t a, uint8x16_t b);    // VSUB.I8 q0,q0,q0 ",
        "uint16x8_t  vsubq_u16(uint16x8_t a, uint16x8_t b);   // VSUB.I16 q0,q0,q0",
        "uint32x4_t  vsubq_u32(uint32x4_t a, uint32x4_t b);   // VSUB.I32 q0,q0,q0",
        "uint64x2_t  vsubq_u64(uint64x2_t a, uint64x2_t b);   // VSUB.I64 q0,q0,q0",
        "int16x8_t  vsubl_s8(int8x8_t a, int8x8_t b);      // VSUBL.S8 q0,d0,d0 ",
        "int32x4_t  vsubl_s16(int16x4_t a, int16x4_t b);   // VSUBL.S16 q0,d0,d0",
        "int64x2_t  vsubl_s32(int32x2_t a, int32x2_t b);   // VSUBL.S32 q0,d0,d0",
        "uint16x8_t vsubl_u8(uint8x8_t a, uint8x8_t b);    // VSUBL.U8 q0,d0,d0 ",
        "uint32x4_t vsubl_u16(uint16x4_t a, uint16x4_t b); // VSUBL.U16 q0,d0,d0",
        "uint64x2_t vsubl_u32(uint32x2_t a, uint32x2_t b); // VSUBL.U32 q0,d0,d0",
        "int16x8_t  vsubw_s8(int16x8_t a, int8x8_t b);     // VSUBW.S8 q0,q0,d0 ",
        "int32x4_t  vsubw_s16(int32x4_t a, int16x4_t b);   // VSUBW.S16 q0,q0,d0",
        "int64x2_t  vsubw_s32(int64x2_t a, int32x2_t b);   // VSUBW.S32 q0,q0,d0",
        "uint16x8_t vsubw_u8(uint16x8_t a, uint8x8_t b);   // VSUBW.U8 q0,q0,d0 ",
        "uint32x4_t vsubw_u16(uint32x4_t a, uint16x4_t b); // VSUBW.U16 q0,q0,d0",
        "uint64x2_t vsubw_u32(uint64x2_t a, uint32x2_t b); // VSUBW.U32 q0,q0,d0"
        ],
    "qsub": [
        "int8x8_t   vqsub_s8(int8x8_t a, int8x8_t b);       // VQSUB.S8 d0,d0,d0 ",
        "int16x4_t  vqsub_s16(int16x4_t a, int16x4_t b);    // VQSUB.S16 d0,d0,d0",
        "int32x2_t  vqsub_s32(int32x2_t a, int32x2_t b);    // VQSUB.S32 d0,d0,d0",
        "int64x1_t  vqsub_s64(int64x1_t a, int64x1_t b);    // VQSUB.S64 d0,d0,d0",
        "uint8x8_t  vqsub_u8(uint8x8_t a, uint8x8_t b);     // VQSUB.U8 d0,d0,d0 ",
        "uint16x4_t vqsub_u16(uint16x4_t a, uint16x4_t b);  // VQSUB.U16 d0,d0,d0",
        "uint32x2_t vqsub_u32(uint32x2_t a, uint32x2_t b);  // VQSUB.U32 d0,d0,d0",
        "uint64x1_t vqsub_u64(uint64x1_t a, uint64x1_t b);  // VQSUB.U64 d0,d0,d0",
        "int8x16_t  vqsubq_s8(int8x16_t a, int8x16_t b);    // VQSUB.S8 q0,q0,q0 ",
        "int16x8_t  vqsubq_s16(int16x8_t a, int16x8_t b);   // VQSUB.S16 q0,q0,q0",
        "int32x4_t  vqsubq_s32(int32x4_t a, int32x4_t b);   // VQSUB.S32 q0,q0,q0",
        "int64x2_t  vqsubq_s64(int64x2_t a, int64x2_t b);   // VQSUB.S64 q0,q0,q0",
        "uint8x16_t vqsubq_u8(uint8x16_t a, uint8x16_t b);  // VQSUB.U8 q0,q0,q0 ",
        "uint16x8_t vqsubq_u16(uint16x8_t a, uint16x8_t b); // VQSUB.U16 q0,q0,q0",
        "uint32x4_t vqsubq_u32(uint32x4_t a, uint32x4_t b); // VQSUB.U32 q0,q0,q0",
        "uint64x2_t vqsubq_u64(uint64x2_t a, uint64x2_t b); // VQSUB.U64 q0,q0,q0"
        ],
    "hsub": [
        "int8x8_t   vhsub_s8(int8x8_t a, int8x8_t b);       // VHSUB.S8 d0,d0,d0 ",
        "int16x4_t  vhsub_s16(int16x4_t a, int16x4_t b);    // VHSUB.S16 d0,d0,d0",
        "int32x2_t  vhsub_s32(int32x2_t a, int32x2_t b);    // VHSUB.S32 d0,d0,d0",
        "uint8x8_t  vhsub_u8(uint8x8_t a, uint8x8_t b);     // VHSUB.U8 d0,d0,d0 ",
        "uint16x4_t vhsub_u16(uint16x4_t a, uint16x4_t b);  // VHSUB.U16 d0,d0,d0",
        "uint32x2_t vhsub_u32(uint32x2_t a, uint32x2_t b);  // VHSUB.U32 d0,d0,d0",
        "int8x16_t  vhsubq_s8(int8x16_t a, int8x16_t b);    // VHSUB.S8 q0,q0,q0 ",
        "int16x8_t  vhsubq_s16(int16x8_t a, int16x8_t b);   // VHSUB.S16 q0,q0,q0",
        "int32x4_t  vhsubq_s32(int32x4_t a, int32x4_t b);   // VHSUB.S32 q0,q0,q0",
        "uint8x16_t vhsubq_u8(uint8x16_t a, uint8x16_t b);  // VHSUB.U8 q0,q0,q0 ",
        "uint16x8_t vhsubq_u16(uint16x8_t a, uint16x8_t b); // VHSUB.U16 q0,q0,q0",
        "uint32x4_t vhsubq_u32(uint32x4_t a, uint32x4_t b); // VHSUB.U32 q0,q0,q0"
        ],
    "subhn": [
        "int8x8_t   vsubhn_s16(int16x8_t a, int16x8_t b);   // VSUBHN.I16 d0,q0,q0",
        "int16x4_t  vsubhn_s32(int32x4_t a, int32x4_t b);   // VSUBHN.I32 d0,q0,q0",
        "int32x2_t  vsubhn_s64(int64x2_t a, int64x2_t b);   // VSUBHN.I64 d0,q0,q0",
        "uint8x8_t  vsubhn_u16(uint16x8_t a, uint16x8_t b); // VSUBHN.I16 d0,q0,q0",
        "uint16x4_t vsubhn_u32(uint32x4_t a, uint32x4_t b); // VSUBHN.I32 d0,q0,q0",
        "uint32x2_t vsubhn_u64(uint64x2_t a, uint64x2_t b); // VSUBHN.I64 d0,q0,q0"
        ],
    "rsubhn": [
        "int8x8_t   vrsubhn_s16(int16x8_t a, int16x8_t b);   // VRSUBHN.I16 d0,q0,q0",
        "int16x4_t  vrsubhn_s32(int32x4_t a, int32x4_t b);   // VRSUBHN.I32 d0,q0,q0",
        "int32x2_t  vrsubhn_s64(int64x2_t a, int64x2_t b);   // VRSUBHN.I64 d0,q0,q0",
        "uint8x8_t  vrsubhn_u16(uint16x8_t a, uint16x8_t b); // VRSUBHN.I16 d0,q0,q0",
        "uint16x4_t vrsubhn_u32(uint32x4_t a, uint32x4_t b); // VRSUBHN.I32 d0,q0,q0",
        "uint32x2_t vrsubhn_u64(uint64x2_t a, uint64x2_t b); // VRSUBHN.I64 d0,q0,q0"
        ],
    "abd": [
        "int8x8_t    vabd_s8(int8x8_t a, int8x8_t b);         // VABD.S8 d0,d0,d0 ",
        "int16x4_t   vabd_s16(int16x4_t a, int16x4_t b);      // VABD.S16 d0,d0,d0",
        "int32x2_t   vabd_s32(int32x2_t a, int32x2_t b);      // VABD.S32 d0,d0,d0",
        "uint8x8_t   vabd_u8(uint8x8_t a, uint8x8_t b);       // VABD.U8 d0,d0,d0 ",
        "uint16x4_t  vabd_u16(uint16x4_t a, uint16x4_t b);    // VABD.U16 d0,d0,d0",
        "uint32x2_t  vabd_u32(uint32x2_t a, uint32x2_t b);    // VABD.U32 d0,d0,d0",
        "float32x2_t vabd_f32(float32x2_t a, float32x2_t b);  // VABD.F32 d0,d0,d0",
        "int8x16_t   vabdq_s8(int8x16_t a, int8x16_t b);      // VABD.S8 q0,q0,q0 ",
        "int16x8_t   vabdq_s16(int16x8_t a, int16x8_t b);     // VABD.S16 q0,q0,q0",
        "int32x4_t   vabdq_s32(int32x4_t a, int32x4_t b);     // VABD.S32 q0,q0,q0",
        "uint8x16_t  vabdq_u8(uint8x16_t a, uint8x16_t b);    // VABD.U8 q0,q0,q0 ",
        "uint16x8_t  vabdq_u16(uint16x8_t a, uint16x8_t b);   // VABD.U16 q0,q0,q0",
        "uint32x4_t  vabdq_u32(uint32x4_t a, uint32x4_t b);   // VABD.U32 q0,q0,q0",
        "float32x4_t vabdq_f32(float32x4_t a, float32x4_t b); // VABD.F32 q0,q0,q0",
        "int16x8_t  vabdl_s8(int8x8_t a, int8x8_t b);      // VABDL.S8 q0,d0,d0 ",
        "int32x4_t  vabdl_s16(int16x4_t a, int16x4_t b);   // VABDL.S16 q0,d0,d0",
        "int64x2_t  vabdl_s32(int32x2_t a, int32x2_t b);   // VABDL.S32 q0,d0,d0",
        "uint16x8_t vabdl_u8(uint8x8_t a, uint8x8_t b);    // VABDL.U8 q0,d0,d0 ",
        "uint32x4_t vabdl_u16(uint16x4_t a, uint16x4_t b); // VABDL.U16 q0,d0,d0",
        "uint64x2_t vabdl_u32(uint32x2_t a, uint32x2_t b); // VABDL.U32 q0,d0,d0"
        ],
    "aba": [
        "int8x8_t   vaba_s8(int8x8_t a, int8x8_t b, int8x8_t c);         // VABA.S8 d0,d0,d0 ",
        "int16x4_t  vaba_s16(int16x4_t a, int16x4_t b, int16x4_t c);     // VABA.S16 d0,d0,d0",
        "int32x2_t  vaba_s32(int32x2_t a, int32x2_t b, int32x2_t c);     // VABA.S32 d0,d0,d0",
        "uint8x8_t  vaba_u8(uint8x8_t a, uint8x8_t b, uint8x8_t c);      // VABA.U8 d0,d0,d0 ",
        "uint16x4_t vaba_u16(uint16x4_t a, uint16x4_t b, uint16x4_t c);  // VABA.U16 d0,d0,d0",
        "uint32x2_t vaba_u32(uint32x2_t a, uint32x2_t b, uint32x2_t c);  // VABA.U32 d0,d0,d0",
        "int8x16_t  vabaq_s8(int8x16_t a, int8x16_t b, int8x16_t c);     // VABA.S8 q0,q0,q0 ",
        "int16x8_t  vabaq_s16(int16x8_t a, int16x8_t b, int16x8_t c);    // VABA.S16 q0,q0,q0",
        "int32x4_t  vabaq_s32(int32x4_t a, int32x4_t b, int32x4_t c);    // VABA.S32 q0,q0,q0",
        "uint8x16_t vabaq_u8(uint8x16_t a, uint8x16_t b, uint8x16_t c);  // VABA.U8 q0,q0,q0 ",
        "uint16x8_t vabaq_u16(uint16x8_t a, uint16x8_t b, uint16x8_t c); // VABA.U16 q0,q0,q0",
        "uint32x4_t vabaq_u32(uint32x4_t a, uint32x4_t b, uint32x4_t c); // VABA.U32 q0,q0,q0",
        "int16x8_t  vabal_s8(int16x8_t a, int8x8_t b, int8x8_t c);       // VABAL.S8 q0,d0,d0 ",
        "int32x4_t  vabal_s16(int32x4_t a, int16x4_t b, int16x4_t c);    // VABAL.S16 q0,d0,d0",
        "int64x2_t  vabal_s32(int64x2_t a, int32x2_t b, int32x2_t c);    // VABAL.S32 q0,d0,d0",
        "uint16x8_t vabal_u8(uint16x8_t a, uint8x8_t b, uint8x8_t c);    // VABAL.U8 q0,d0,d0 ",
        "uint32x4_t vabal_u16(uint32x4_t a, uint16x4_t b, uint16x4_t c); // VABAL.U16 q0,d0,d0",
        "uint64x2_t vabal_u32(uint64x2_t a, uint32x2_t b, uint32x2_t c); // VABAL.U32 q0,d0,d0"
        ],
    "max": [
        "int8x8_t    vmax_s8(int8x8_t a, int8x8_t b);         // VMAX.S8 d0,d0,d0 ",
        "int16x4_t   vmax_s16(int16x4_t a, int16x4_t b);      // VMAX.S16 d0,d0,d0",
        "int32x2_t   vmax_s32(int32x2_t a, int32x2_t b);      // VMAX.S32 d0,d0,d0",
        "uint8x8_t   vmax_u8(uint8x8_t a, uint8x8_t b);       // VMAX.U8 d0,d0,d0 ",
        "uint16x4_t  vmax_u16(uint16x4_t a, uint16x4_t b);    // VMAX.U16 d0,d0,d0",
        "uint32x2_t  vmax_u32(uint32x2_t a, uint32x2_t b);    // VMAX.U32 d0,d0,d0",
        "float32x2_t vmax_f32(float32x2_t a, float32x2_t b);  // VMAX.F32 d0,d0,d0",
        "int8x16_t   vmaxq_s8(int8x16_t a, int8x16_t b);      // VMAX.S8 q0,q0,q0 ",
        "int16x8_t   vmaxq_s16(int16x8_t a, int16x8_t b);     // VMAX.S16 q0,q0,q0",
        "int32x4_t   vmaxq_s32(int32x4_t a, int32x4_t b);     // VMAX.S32 q0,q0,q0",
        "uint8x16_t  vmaxq_u8(uint8x16_t a, uint8x16_t b);    // VMAX.U8 q0,q0,q0 ",
        "uint16x8_t  vmaxq_u16(uint16x8_t a, uint16x8_t b);   // VMAX.U16 q0,q0,q0",
        "uint32x4_t  vmaxq_u32(uint32x4_t a, uint32x4_t b);   // VMAX.U32 q0,q0,q0",
        "float32x4_t vmaxq_f32(float32x4_t a, float32x4_t b); // VMAX.F32 q0,q0,q0"
    ],
                                            "min": [
                                                "int8x8_t    vmin_s8(int8x8_t a, int8x8_t b);         // VMIN.S8 d0,d0,d0 ",
                                                "int16x4_t   vmin_s16(int16x4_t a, int16x4_t b);      // VMIN.S16 d0,d0,d0",
                                                "int32x2_t   vmin_s32(int32x2_t a, int32x2_t b);      // VMIN.S32 d0,d0,d0",
                                                "uint8x8_t   vmin_u8(uint8x8_t a, uint8x8_t b);       // VMIN.U8 d0,d0,d0 ",
                                                "uint16x4_t  vmin_u16(uint16x4_t a, uint16x4_t b);    // VMIN.U16 d0,d0,d0",
                                                "uint32x2_t  vmin_u32(uint32x2_t a, uint32x2_t b);    // VMIN.U32 d0,d0,d0",
                                                "float32x2_t vmin_f32(float32x2_t a, float32x2_t b);  // VMIN.F32 d0,d0,d0",
                                                "int8x16_t   vminq_s8(int8x16_t a, int8x16_t b);      // VMIN.S8 q0,q0,q0 ",
                                                "int16x8_t   vminq_s16(int16x8_t a, int16x8_t b);     // VMIN.S16 q0,q0,q0",
                                                "int32x4_t   vminq_s32(int32x4_t a, int32x4_t b);     // VMIN.S32 q0,q0,q0",
                                                "uint8x16_t  vminq_u8(uint8x16_t a, uint8x16_t b);    // VMIN.U8 q0,q0,q0 ",
                                            "uint16x8_t  vminq_u16(uint16x8_t a, uint16x8_t b);   // VMIN.U16 q0,q0,q0",
                                                                                                    "uint32x4_t  vminq_u32(uint32x4_t a, uint32x4_t b);   // VMIN.U32 q0,q0,q0",
                                                                                                        "float32x4_t vminq_f32(float32x4_t a, float32x4_t b); // VMIN.F32 q0,q0,q0"
                                                                                                          ]
                                            }
