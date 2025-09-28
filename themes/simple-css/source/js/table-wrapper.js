// Auto-wrap tables that don't already have horizontal scroll protection
document.addEventListener('DOMContentLoaded', function() {
    const tables = document.querySelectorAll('table');
    
    tables.forEach(function(table) {
        // Check if table is already wrapped
        const parent = table.parentElement;
        const hasOverflowWrapper = parent.style.overflowX === 'auto' || 
                                   parent.classList.contains('table-wrapper') ||
                                   parent.classList.contains('auto-table-wrapper') ||
                                   parent.getAttribute('style')?.includes('overflow-x:auto');
        
        // If not already wrapped, wrap it
        if (!hasOverflowWrapper) {
            const wrapper = document.createElement('div');
            wrapper.className = 'auto-table-wrapper';
            
            // Insert wrapper before table
            table.parentNode.insertBefore(wrapper, table);
            
            // Move table into wrapper
            wrapper.appendChild(table);
        }
    });
});
