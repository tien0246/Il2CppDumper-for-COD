using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using static Il2CppDumper.ElfConstants;

namespace Il2CppDumper
{
    public sealed class Elf64 : ElfBase
    {
        private Elf64_Ehdr elfHeader;
        private Elf64_Phdr[] programSegment;
        private Elf64_Dyn[] dynamicSection;
        private Elf64_Sym[] symbolTable;
        private Elf64_Shdr[] sectionTable;
        private Elf64_Phdr pt_dynamic;

        public Elf64(Stream stream) : base(stream)
        {
            Load();
        }

        protected override void Load()
        {
            elfHeader = ReadClass<Elf64_Ehdr>(0);
            programSegment = ReadClassArray<Elf64_Phdr>(elfHeader.e_phoff, elfHeader.e_phnum);
            if (IsDumped)
            {
                FixedProgramSegment();
            }
            pt_dynamic = programSegment.First(x => x.p_type == PT_DYNAMIC);
            dynamicSection = ReadClassArray<Elf64_Dyn>(pt_dynamic.p_offset, pt_dynamic.p_filesz / 16L);
            if (IsDumped)
            {
                FixedDynamicSection();
            }
            ReadSymbol();
            if (!IsDumped)
            {
                RelocationProcessing();
                if (CheckProtection())
                {
                    Console.WriteLine("ERROR: This file may be protected.");
                }
            }
        }

        protected override bool CheckSection()
        {
            try
            {
                var names = new List<string>();
                sectionTable = ReadClassArray<Elf64_Shdr>(elfHeader.e_shoff, elfHeader.e_shnum);
                var shstrndx = sectionTable[elfHeader.e_shstrndx].sh_offset;
                foreach (var section in sectionTable)
                {
                    names.Add(ReadStringToNull(shstrndx + section.sh_name));
                }
                if (!names.Contains(".text"))
                {
                    return false;
                }
                return true;
            }
            catch
            {
                return false;
            }
        }

        public override ulong MapVATR(ulong addr)
        {
            var phdr = programSegment.First(x => addr >= x.p_vaddr && addr <= x.p_vaddr + x.p_memsz);
            return addr - phdr.p_vaddr + phdr.p_offset;
        }

        public override ulong MapRTVA(ulong addr)
        {
            var phdr = programSegment.FirstOrDefault(x => addr >= x.p_offset && addr <= x.p_offset + x.p_filesz);
            if (phdr == null)
            {
                return 0;
            }
            return addr - phdr.p_offset + phdr.p_vaddr;
        }

        public override bool Search()
        {
            return false;
        }

        public override bool PlusSearch(int methodCount, int typeDefinitionsCount, int imageCount)
        {
            var sectionHelper = GetSectionHelper(methodCount, typeDefinitionsCount, imageCount);
            var codeRegistration = sectionHelper.FindCodeRegistration();
            var metadataRegistration = sectionHelper.FindMetadataRegistration();
            return AutoPlusInit(codeRegistration, metadataRegistration);
        }

        public override bool SymbolSearch()
        {
            ulong codeRegistration = 0ul;
            ulong metadataRegistration = 0ul;
            ulong dynstrOffset = MapVATR(dynamicSection.First(x => x.d_tag == DT_STRTAB).d_un);
            foreach (var symbol in symbolTable)
            {
                var name = ReadStringToNull(dynstrOffset + symbol.st_name);
                switch (name)
                {
                    case "g_CodeRegistration":
                        codeRegistration = symbol.st_value;
                        break;
                    case "g_MetadataRegistration":
                        metadataRegistration = symbol.st_value;
                        break;
                }
            }
            if (codeRegistration > 0 && metadataRegistration > 0)
            {
                Console.WriteLine("Detected Symbol !");
                Console.WriteLine("CodeRegistration : {0:x}", codeRegistration);
                Console.WriteLine("MetadataRegistration : {0:x}", metadataRegistration);
                Init(codeRegistration, metadataRegistration);
                return true;
            }
            Console.WriteLine("ERROR: No symbol is detected");
            return false;
        }

        private void ReadSymbol()
        {
            try
            {
                var symbolCount = 0u;
                var hash = dynamicSection.FirstOrDefault(x => x.d_tag == DT_HASH);
                if (hash != null)
                {
                    var addr = MapVATR(hash.d_un);
                    Position = addr;
                    var nbucket = ReadUInt32();
                    var nchain = ReadUInt32();
                    symbolCount = nchain;
                }
                else
                {
                    hash = dynamicSection.First(x => x.d_tag == DT_GNU_HASH);
                    var addr = MapVATR(hash.d_un);
                    Position = addr;
                    var nbuckets = ReadUInt32();
                    var symoffset = ReadUInt32();
                    var bloom_size = ReadUInt32();
                    var bloom_shift = ReadUInt32();
                    var buckets_address = addr + 16 + (8 * bloom_size);
                    var buckets = ReadClassArray<uint>(buckets_address, nbuckets);
                    var last_symbol = buckets.Max();
                    if (last_symbol < symoffset)
                    {
                        symbolCount = symoffset;
                    }
                    else
                    {
                        var chains_base_address = buckets_address + 4 * nbuckets;
                        Position = chains_base_address + (last_symbol - symoffset) * 4;
                        while (true)
                        {
                            var chain_entry = ReadUInt32();
                            ++last_symbol;
                            if ((chain_entry & 1) != 0)
                                break;
                        }
                        symbolCount = last_symbol;
                    }
                }
                var dynsymOffset = MapVATR(dynamicSection.First(x => x.d_tag == DT_SYMTAB).d_un);
                symbolTable = ReadClassArray<Elf64_Sym>(dynsymOffset, symbolCount);
            }
            catch
            {
                // ignored
            }
        }

        // https://android.googlesource.com/platform/bionic/+/refs/heads/main/linker/linker_reloc_iterators.h
        // https://android.googlesource.com/platform/bionic/+/refs/heads/main/linker/linker_reloc_iterators.h
        private List<Elf64_Rela> ReadAndroidRelocations(ulong offset, ulong size)
        {
            const ulong RELOCATION_GROUPED_BY_INFO_FLAG = 1;
            const ulong RELOCATION_GROUPED_BY_OFFSET_DELTA_FLAG = 2;
            const ulong RELOCATION_GROUPED_BY_ADDEND_FLAG = 4;
            const ulong RELOCATION_GROUP_HAS_ADDEND_FLAG = 8;

            var result = new List<Elf64_Rela>();
            Position = offset;

            var magic = ReadBytes(4);
            if (magic[0] != 'A' || magic[1] != 'P' || magic[2] != 'S' || magic[3] != '2')
            {
                return result;
            }

            ulong numRelocs = ReadSleb128();
            var reloc = new Elf64_Rela
            {
                r_offset = ReadSleb128()
            };

            for (ulong idx = 0; idx < numRelocs;)
            {
                ulong groupSize = ReadSleb128();
                ulong groupFlags = ReadSleb128();

                ulong groupROffsetDelta = 0;
                if ((groupFlags & RELOCATION_GROUPED_BY_OFFSET_DELTA_FLAG) != 0)
                {
                    groupROffsetDelta = ReadSleb128();
                }

                if ((groupFlags & RELOCATION_GROUPED_BY_INFO_FLAG) != 0)
                {
                    reloc.r_info = ReadSleb128();
                }

                ulong groupFlagsReloc = groupFlags & (RELOCATION_GROUP_HAS_ADDEND_FLAG | RELOCATION_GROUPED_BY_ADDEND_FLAG);
                if (groupFlagsReloc == RELOCATION_GROUP_HAS_ADDEND_FLAG)
                {
                    // Each relocation has an addend. This is the default situation with lld's current encoder.
                }
                else if (groupFlagsReloc == (RELOCATION_GROUP_HAS_ADDEND_FLAG | RELOCATION_GROUPED_BY_ADDEND_FLAG))
                {
                    reloc.r_addend += ReadSleb128();
                }
                else
                {
                    reloc.r_addend = 0;
                }

                for (ulong i = 0; i < groupSize; i++)
                {
                    if ((groupFlags & RELOCATION_GROUPED_BY_OFFSET_DELTA_FLAG) != 0)
                    {
                        reloc.r_offset += groupROffsetDelta;
                    }
                    else
                    {
                        reloc.r_offset += ReadSleb128();
                    }

                    if ((groupFlags & RELOCATION_GROUPED_BY_INFO_FLAG) == 0)
                    {
                        reloc.r_info = ReadSleb128();
                    }

                    if (groupFlagsReloc == RELOCATION_GROUP_HAS_ADDEND_FLAG)
                    {
                        reloc.r_addend += ReadSleb128();
                    }

                    result.Add(new Elf64_Rela
                    {
                        r_offset = reloc.r_offset,
                        r_info = reloc.r_info,
                        r_addend = reloc.r_addend
                    });
                }

                idx += groupSize;
            }

            return result;
        }
        private ulong ReadSleb128()
        {
            ulong value = 0;
            int shift = 0;
            byte b;
            do
            {
                b = ReadByte();
                value |= (ulong)(b & 0x7f) << shift;
                shift += 7;
            } while ((b & 0x80) != 0);

            if (shift < 64 && (b & 0x40) != 0)
                value |= ~0UL << shift;

            return value;
        }

        private void RelocationProcessing()
        {
            Console.WriteLine("Applying relocations...");
            try
            {
                var relaTable = new List<Elf64_Rela>();
                if (dynamicSection.Any(x => x.d_tag == DT_RELA))
                {
                    var relaOffset = MapVATR(dynamicSection.First(x => x.d_tag == DT_RELA).d_un);
                    var relaSize = dynamicSection.First(x => x.d_tag == DT_RELASZ).d_un;
                    relaTable.AddRange(ReadClassArray<Elf64_Rela>(relaOffset, relaSize / 24L));
                }

                if (dynamicSection.Any(x => x.d_tag == DT_ANDROID_RELA))
                {
                    var androidRelaOffset = MapVATR(dynamicSection.First(x => x.d_tag == DT_ANDROID_RELA).d_un);
                    var androidRelaSize = dynamicSection.First(x => x.d_tag == DT_ANDROID_RELASZ).d_un;
                    relaTable.AddRange(ReadAndroidRelocations(androidRelaOffset, androidRelaSize));
                }

                foreach (var rela in relaTable)
                {
                    var type = rela.r_info & 0xffffffff;
                    var sym = rela.r_info >> 32;
                    (ulong value, bool recognized) result = (type, elfHeader.e_machine) switch
                    {
                        (R_AARCH64_ABS64, EM_AARCH64) => (symbolTable[sym].st_value + rela.r_addend, true),
                        (R_AARCH64_RELATIVE, EM_AARCH64) => (rela.r_addend, true),

                        (R_X86_64_64, EM_X86_64) => (symbolTable[sym].st_value + rela.r_addend, true),
                        (R_X86_64_RELATIVE, EM_X86_64) => (rela.r_addend, true),

                        _ => (0, false)
                    };
                    if (result.recognized)
                    {
                        Position = MapVATR(rela.r_offset);
                        Write(result.value);
                    }
                }
            }
            catch
            {
                // ignored
            }
        }

        private bool CheckProtection()
        {
            try
            {
                //.init_proc
                if (dynamicSection.Any(x => x.d_tag == DT_INIT))
                {
                    Console.WriteLine("WARNING: find .init_proc");
                    return true;
                }
                //JNI_OnLoad
                ulong dynstrOffset = MapVATR(dynamicSection.First(x => x.d_tag == DT_STRTAB).d_un);
                foreach (var symbol in symbolTable)
                {
                    var name = ReadStringToNull(dynstrOffset + symbol.st_name);
                    switch (name)
                    {
                        case "JNI_OnLoad":
                            Console.WriteLine("WARNING: find JNI_OnLoad");
                            return true;
                    }
                }
                if (sectionTable != null && sectionTable.Any(x => x.sh_type == SHT_LOUSER))
                {
                    Console.WriteLine("WARNING: find SHT_LOUSER section");
                    return true;
                }
            }
            catch
            {
                // ignored
            }
            return false;
        }

        public override ulong GetRVA(ulong pointer)
        {
            if (IsDumped)
            {
                return pointer - ImageBase;
            }
            return pointer;
        }

        private void FixedProgramSegment()
        {
            for (uint i = 0; i < programSegment.Length; i++)
            {
                Position = elfHeader.e_phoff + i * 56u + 8u;
                var phdr = programSegment[i];
                phdr.p_offset = phdr.p_vaddr;
                Write(phdr.p_offset);
                phdr.p_vaddr += ImageBase;
                Write(phdr.p_vaddr);
                Position += 8;
                phdr.p_filesz = phdr.p_memsz;
                Write(phdr.p_filesz);
            }
        }

        private void FixedDynamicSection()
        {
            for (uint i = 0; i < dynamicSection.Length; i++)
            {
                Position = pt_dynamic.p_offset + i * 16 + 8;
                var dyn = dynamicSection[i];
                switch (dyn.d_tag)
                {
                    case DT_PLTGOT:
                    case DT_HASH:
                    case DT_STRTAB:
                    case DT_SYMTAB:
                    case DT_RELA:
                    case DT_INIT:
                    case DT_FINI:
                    case DT_REL:
                    case DT_JMPREL:
                    case DT_INIT_ARRAY:
                    case DT_FINI_ARRAY:
                        dyn.d_un += ImageBase;
                        Write(dyn.d_un);
                        break;
                }
            }
        }

        public override SectionHelper GetSectionHelper(int methodCount, int typeDefinitionsCount, int imageCount)
        {
            var dataList = new List<Elf64_Phdr>();
            var execList = new List<Elf64_Phdr>();
            foreach (var phdr in programSegment)
            {
                if (phdr.p_memsz != 0ul)
                {
                    switch (phdr.p_flags)
                    {
                        case 1u: //PF_X
                        case 3u:
                        case 5u:
                        case 7u:
                            execList.Add(phdr);
                            break;
                        case 2u: //PF_W && PF_R
                        case 4u:
                        case 6u:
                            dataList.Add(phdr);
                            break;
                    }
                }
            }
            var data = dataList.ToArray();
            var exec = execList.ToArray();
            var sectionHelper = new SectionHelper(this, methodCount, typeDefinitionsCount, metadataUsagesCount, imageCount);
            sectionHelper.SetSection(SearchSectionType.Exec, exec);
            sectionHelper.SetSection(SearchSectionType.Data, data);
            sectionHelper.SetSection(SearchSectionType.Bss, data);
            return sectionHelper;
        }
    }
}
