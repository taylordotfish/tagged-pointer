/*
 * Copyright 2021-2024 taylor.fish <contact@taylor.fish>
 *
 * This file is part of tagged-pointer.
 *
 * tagged-pointer is licensed under the Apache License, Version 2.0
 * (the "License"); you may not use tagged-pointer except in compliance
 * with the License. You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#[rustfmt::skip]
macro_rules! compile_fail_doctest {
    (
        $name:ident,
        pass = $pass:literal,
        fail = $fail:literal,
        $code:literal $(,)?
    ) => {
        /// ```
        #[doc = $pass]
        #[doc = $code]
        /// ```
        ///
        /// ```compile_fail
        #[doc = $fail]
        #[doc = $code]
        /// ```
        mod $name {}
    };
}

mod type_not_aligned_enough {
    compile_fail_doctest! {
        test1,
        pass = "const BITS: usize = 0;",
        fail = "const BITS: usize = 1;",
        r"use tagged_pointer::TaggedPtr;
        TaggedPtr::<_, BITS>::new((&0_u8).into(), 0);",
    }

    compile_fail_doctest! {
        test2,
        pass = "const BITS: usize = 1;",
        fail = "const BITS: usize = 2;",
        r"use tagged_pointer::TaggedPtr;
        #[repr(align(2))]
        struct Align2(pub u16);
        TaggedPtr::<_, BITS>::new((&Align2(0)).into(), 0);",
    }

    compile_fail_doctest! {
        test3,
        pass = "const BITS: usize = 2;",
        fail = "const BITS: usize = 3;",
        r"use tagged_pointer::TaggedPtr;
        #[repr(align(4))]
        struct Align4(pub u32);
        TaggedPtr::<_, BITS>::new((&Align4(0)).into(), 0);",
    }

    compile_fail_doctest! {
        test4,
        pass = "const BITS: usize = 3;",
        fail = "const BITS: usize = 4;",
        r"use tagged_pointer::TaggedPtr;
        #[repr(align(8))]
        struct Align8(pub u64);
        TaggedPtr::<_, BITS>::new((&Align8(0)).into(), 0);",
    }
}
